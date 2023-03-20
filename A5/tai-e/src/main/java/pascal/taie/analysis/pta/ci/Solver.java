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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.contains(method))
            return;
        callGraph.addReachableMethod(method);
        method.getIR().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New newStmt) {
            PointsToSet pts = new PointsToSet(heapModel.getObj( newStmt));
            VarPtr x = pointerFlowGraph.getVarPtr( newStmt.getLValue());
            workList.addEntry(x, pts);
            return StmtVisitor.super.visit( newStmt);
        }

        @Override
        public Void visit(Copy copy) {
            VarPtr x = pointerFlowGraph.getVarPtr(copy.getLValue());
            VarPtr y = pointerFlowGraph.getVarPtr(copy.getRValue());
            addPFGEdge(y, x);
            return StmtVisitor.super.visit(copy);
        }

        @Override
        public Void visit(LoadField load) {
            if (load.isStatic()) {
                VarPtr y = pointerFlowGraph.getVarPtr(load.getLValue());
                Pointer field = pointerFlowGraph.getStaticField(load.getFieldRef().resolve());
                addPFGEdge(field, y);
            }
            return StmtVisitor.super.visit(load);
        }

        @Override
        public Void visit(StoreField store) {
            if (store.isStatic()) {
                VarPtr y = pointerFlowGraph.getVarPtr(store.getRValue());
                Pointer field = pointerFlowGraph.getStaticField(store.getFieldRef().resolve());
                addPFGEdge(y, field);
            }
            return StmtVisitor.super.visit(store);
        }

        @Override
        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                JMethod m = resolveCallee(null, invoke);


                if (!callGraph.getCalleesOf(invoke).contains(m)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                    addReachable(m);
                    for (int i = 0; i < m.getParamCount(); i++) {
                        VarPtr a = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                        VarPtr p = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));
                        addPFGEdge(a, p);
                    }

                    if (invoke.getLValue() != null)
                        m.getIR().getReturnVars().forEach(ret ->
                                addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                                        pointerFlowGraph.getVarPtr(invoke.getLValue())));
                }
            }
            return StmtVisitor.super.visit(invoke);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.getSuccsOf(source).contains(target))
            return;

        pointerFlowGraph.addEdge(source, target);
        if (!source.getPointsToSet().isEmpty())
            workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry item = workList.pollEntry();
            PointsToSet delta = propagate(item.pointer(), item.pointsToSet());

            if (item.pointer() instanceof VarPtr ptr) {
                Var var = ptr.getVar();
                delta.forEach(obj -> {
                    // field store
                    var.getStoreFields().forEach(s -> addPFGEdge(
                            pointerFlowGraph.getVarPtr(s.getRValue()),
                            pointerFlowGraph.getInstanceField(obj, s.getFieldRef().resolve())
                    ));

                    // field load
                    var.getLoadFields().forEach(s -> addPFGEdge(
                            pointerFlowGraph.getInstanceField(obj, s.getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(s.getLValue())
                    ));

                    // array store
                    var.getStoreArrays().forEach(s -> addPFGEdge(
                            pointerFlowGraph.getVarPtr(s.getRValue()),
                            pointerFlowGraph.getArrayIndex(obj)
                    ));

                    // array load
                    var.getLoadArrays().forEach(s -> addPFGEdge(
                            pointerFlowGraph.getArrayIndex(obj),
                            pointerFlowGraph.getVarPtr(s.getLValue())
                    ));

                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet n = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();

        // calculate delat
        pointsToSet.forEach(obj -> {
            if (!n.contains(obj))
                delta.addObject(obj);
        });

        // propagate
        if (!pointsToSet.isEmpty()) {
            delta.forEach(n::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(invoke -> {
            JMethod m = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()),
                    new PointsToSet(recv));

            // calculate points-to relationship
            if (!callGraph.getCalleesOf(invoke).contains(m)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                addReachable(m);

                // parameters and arguments
                for (int i = 0; i < m.getParamCount(); i++) {
                    VarPtr a = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                    VarPtr p = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));
                    addPFGEdge(a, p);
                }

                // return values
                if (invoke.getLValue() != null)
                    m.getIR().getReturnVars().forEach(ret ->
                            addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                                    pointerFlowGraph.getVarPtr(invoke.getLValue())));
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
