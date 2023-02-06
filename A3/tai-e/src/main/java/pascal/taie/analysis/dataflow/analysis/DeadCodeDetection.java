/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // Your task is to recognize dead code in ir and add it to deadCode

        //============
        // unreachable
        //============
        HashSet<Map.Entry<Stmt, Stmt>> prunedEdges = new HashSet<>(); // track pruned edges
        for (Stmt stmt : ir.getStmts()) {
            // handle if statement
            if (stmt instanceof If ifStmt) {
                // calculate condition value
                Value v = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getResult(stmt));
                if (!v.isConstant()) continue;

                if (v.getConstant() == 0) { // if-true is deadcode
                    prunedEdges.add(Map.entry(stmt, ifStmt.getTarget()));
                } else { // if-false is deadcode
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt))
                        if (edge.getKind() == Edge.Kind.IF_FALSE)
                            prunedEdges.add(Map.entry(stmt, edge.getTarget()));
                }
            }

            // handle switch statement
            else if (stmt instanceof SwitchStmt switchStmt) {
                // calculate switch value
                Value v = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getResult(stmt));
                if (!v.isConstant()) continue;

                boolean match = false; // indicate if case value is matched
                for (Pair<Integer, Stmt> casePair : switchStmt.getCaseTargets()) {
                    if (v.getConstant() == casePair.first()) match = true; // matched case value, prune default edge
                    else prunedEdges.add(Map.entry(stmt, casePair.second()));
                }

                if (match) prunedEdges.add(Map.entry(stmt, switchStmt.getDefaultTarget()));
            }
        }

        // bfs pruning
        HashSet<Stmt> visited = new HashSet<>();
        LinkedList<Stmt> toVisit = new LinkedList<>();
        toVisit.add(cfg.getEntry());

        while (!toVisit.isEmpty()) {
            Stmt node = toVisit.pop();
            visited.add(node);

            for (Stmt adjacent : cfg.getSuccsOf(node))
                // visit non-pruned adjacent nodes
                if (!visited.contains(adjacent) && !prunedEdges.contains(Map.entry(node, adjacent)))
                    toVisit.add(adjacent);
        }
        deadCode.addAll(cfg.getNodes());
        deadCode.remove(cfg.getExit()); // should not include exit node
        deadCode.removeAll(visited);


        //================
        // dead assignment
        //================
        for (Stmt stmt : ir.getStmts()) {
            if (deadCode.contains(stmt)) continue;

            if (stmt instanceof AssignStmt<?, ?> assignStmt         // assignment
                    && assignStmt.getLValue() instanceof Var var    // left value is a var
                    && !liveVars.getResult(stmt).contains(var)      // not a living variable
                    && hasNoSideEffect(assignStmt.getRValue()))     // right value has no side effect
                deadCode.add(stmt);
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
