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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;
    private HashMap<Var, HashSet<Var>> aliasMap; // maintain the possible alias to a variable
    private HashMap<Pair<?, ?>, Value> valMap = new HashMap<>(); // alias-relative values
    private HashMap<Pair<JClass, FieldRef>, HashSet<LoadField>> staticLoadMap = new HashMap<>(); // maintain relative static field

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        buildAliasMap();
        buildStaticLoadMap();
    }

    private void buildAliasMap() {
        aliasMap = new HashMap<>();
        pta.getVars().forEach(var -> {
            HashSet<Var> aliasSet = aliasMap.getOrDefault(var, new HashSet<>());
            aliasSet.add(var);

            pta.getVars().forEach(mayAlias -> {
                if (!Collections.disjoint(pta.getPointsToSet(var),
                        pta.getPointsToSet(mayAlias)))
                    aliasSet.add(mayAlias); // if two PTS join, construct aliasMap
            });

            aliasMap.put(var, aliasSet);
        });
    }

    private void buildStaticLoadMap() {
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access){
                Pair<JClass, FieldRef> key = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                HashSet<LoadField> loadFields = staticLoadMap.getOrDefault(key, new HashSet<>());
                loadFields.add(s);
                staticLoadMap.put(key, loadFields);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);

        return !old.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // process store statement
        StmtProcessor stmtProcessor = new StmtProcessor(in);
        stmt.accept(stmtProcessor);

        // patched transferNode
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);

        if (stmt instanceof DefinitionStmt<?, ?> def) {
            if (def.getLValue() instanceof Var var && ConstantPropagation.canHoldInt(var)) {
                out.remove(var);    // kill

                if (def.getRValue() != null) {
                    Value eval = evaluate(def.getRValue(), in); // gen
                    if (eval != null)
                        out.update(var, eval);
                }
            }
        }

        return !old.equals(out);
    }


    /**
     * Processes store statements to maintain alias information
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        private final CPFact in;

        private StmtProcessor(CPFact in) {
            this.in = in;
        }

        @Override
        public Void visit(StoreArray stmt) {
            Var base = stmt.getArrayAccess().getBase();
            Value index = ConstantPropagation.evaluate(stmt.getArrayAccess().getIndex(), in);

            if (index.isUndef() || !ConstantPropagation.canHoldInt(stmt.getRValue()))
                return StmtVisitor.super.visit(stmt);

            pta.getPointsToSet(base).forEach(obj -> {
                Pair<Obj, Value> key = new Pair<>(obj, index);
                Value v = valMap.getOrDefault(key, Value.getUndef());
                Value newV = cp.meetValue(v, evaluate(stmt.getRValue(), in));
                valMap.put(key, newV);
                if (v != newV) {
                    aliasMap.get(base).forEach(var -> solver.workList.addAll(var.getLoadArrays()));
                }
            });


            return StmtVisitor.super.visit(stmt);
        }


        @Override
        public Void visit(StoreField stmt) {
            if (!ConstantPropagation.canHoldInt(stmt.getRValue()))
                return StmtVisitor.super.visit(stmt);

            if (stmt.getFieldAccess() instanceof InstanceFieldAccess instanceAccess) {
                Var base = instanceAccess.getBase();
                pta.getPointsToSet(base).forEach(obj -> {
                    Pair<Obj, FieldRef> key = new Pair<>(obj, instanceAccess.getFieldRef());
                    Value v = valMap.getOrDefault(key, Value.getUndef());
                    Value newV = cp.meetValue(v, evaluate(stmt.getRValue(), in));
                    valMap.put(key, newV);
                    if (v != newV) {
                        aliasMap.get(base).forEach(var -> var.getLoadFields().forEach(loadStmt -> {
                            if (loadStmt.getFieldAccess().getFieldRef() == stmt.getFieldRef())
                                solver.workList.add(loadStmt);
                        }));
                    }
                });
            } else if (stmt.getFieldAccess() instanceof StaticFieldAccess access) {
                JClass c = access.getFieldRef().getDeclaringClass();
                Pair<JClass, FieldRef> key = new Pair<>(c, access.getFieldRef());
                Value v = valMap.getOrDefault(key, Value.getUndef());
                Value newV = cp.meetValue(v, evaluate(stmt.getRValue(), in));
                valMap.put(key, newV);
                if (v != newV)
                    solver.workList.addAll(staticLoadMap.getOrDefault(key, new HashSet<>()));
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact res = out.copy();

        if (edge.getSource() instanceof Invoke invoke) {
            if (invoke.getResult() != null)
                res.remove(invoke.getResult());
        }

        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact res = newInitialFact();

        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        for (int i = 0; i < edge.getCallee().getParamCount(); i++) {
            Var arg = invokeExp.getArg(i);
            Var param = edge.getCallee().getIR().getParam(i);
            res.update(param, callSiteOut.get(arg));
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact res = newInitialFact();

        Invoke invoke = (Invoke) edge.getCallSite();
        if (invoke.getResult() != null) {
            Value value = Value.getUndef();

            // meet all return values
            for (Var returnVar : edge.getReturnVars())
                value = cp.meetValue(value, returnOut.get(returnVar));

            res.update(invoke.getResult(), value);
        }

        return res;
    }

    // wrapper function of evaluate to handle field and array access
    private Value evaluate(Exp exp, CPFact in) {
        Value v = Value.getUndef();
        if (exp instanceof InstanceFieldAccess access) {
            Var base = access.getBase();
            for (Obj obj : pta.getPointsToSet(base)) {
                v = cp.meetValue(v, valMap.getOrDefault(new Pair<>(obj, access.getFieldRef()), Value.getUndef()));
            }
        } else if (exp instanceof StaticFieldAccess access) {
            v = valMap.getOrDefault(
                    new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef()),
                    Value.getUndef()
            );
        } else if (exp instanceof ArrayAccess access) {
            Var base = access.getBase();
            Value idx = ConstantPropagation.evaluate(access.getIndex(), in);
            if (idx.isConstant()) {
                for (Obj obj : pta.getPointsToSet(base)) {
                    v = cp.meetValue(v, valMap.getOrDefault(new Pair<>(obj, idx), Value.getUndef()));
                    v = cp.meetValue(v, valMap.getOrDefault(new Pair<>(obj, Value.getNAC()), Value.getUndef()));
                }
            } else if (idx.isNAC()) {
                for (Obj obj : pta.getPointsToSet(base)) {
                    for (Map.Entry<Pair<?, ?>, Value> entry : valMap.entrySet()) {
                        Pair<?, ?> accessPair = entry.getKey();
                        if (accessPair.first().equals(obj) && accessPair.second() instanceof Value) {
                            v = cp.meetValue(v, entry.getValue());
                        }
                    }
                }
            }
        } else {
            v = ConstantPropagation.evaluate(exp, in);  // fallback to `cp.evaluate`
        }
        return v;
    }
}
