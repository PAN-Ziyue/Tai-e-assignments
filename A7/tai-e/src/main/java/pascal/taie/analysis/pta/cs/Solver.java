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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.contains(csMethod))
            return;
        callGraph.addReachableMethod(csMethod);
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            CSVar x = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(ctx, obj));
            workList.addEntry(x, pts);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar x = csManager.getCSVar(context, stmt.getLValue());
            CSVar y = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(y, x);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                CSVar y = csManager.getCSVar(context, stmt.getLValue());
                StaticField field = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(field, y);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                CSVar x = csManager.getCSVar(context, stmt.getRValue());
                StaticField field = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(x, field);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                JMethod m = resolveCallee(null, invoke);
                CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
                Context ctx = contextSelector.selectContext(csCallSite, m);
                CSMethod csm = csManager.getCSMethod(ctx, m);

                if (!callGraph.getCalleesOf(csCallSite).contains(csm)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csm));
                    addReachable(csm);

                    for (int i = 0; i < m.getParamCount(); i++) {
                        CSVar a = csManager.getCSVar(csCallSite.getContext(), invoke.getInvokeExp().getArg(i));
                        CSVar p = csManager.getCSVar(ctx, m.getIR().getParam(i));
                        addPFGEdge(a, p);
                    }

                    if (invoke.getLValue() != null)
                        m.getIR().getReturnVars().forEach(ret ->
                                addPFGEdge(csManager.getCSVar(ctx, ret),
                                        csManager.getCSVar(csCallSite.getContext(), invoke.getLValue())));
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

            if (item.pointer() instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context ctx = csVar.getContext();
                delta.forEach(obj -> {
                    // field store
                    var.getStoreFields().forEach(s -> addPFGEdge(
                            csManager.getCSVar(ctx, s.getRValue()),
                            csManager.getInstanceField(obj, s.getFieldRef().resolve())
                    ));

                    // field load
                    var.getLoadFields().forEach(s -> addPFGEdge(
                            csManager.getInstanceField(obj, s.getFieldRef().resolve()),
                            csManager.getCSVar(ctx, s.getLValue())
                    ));

                    // array store
                    var.getStoreArrays().forEach(s -> addPFGEdge(
                            csManager.getCSVar(ctx, s.getRValue()),
                            csManager.getArrayIndex(obj)
                    ));

                    // array load
                    var.getLoadArrays().forEach(s -> addPFGEdge(
                            csManager.getArrayIndex(obj),
                            csManager.getCSVar(ctx, s.getLValue())
                    ));

                    processCall(csVar, obj);
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
        PointsToSet delta = PointsToSetFactory.make();

        // calculate delta
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(invoke -> {
            JMethod m = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context ctx =  contextSelector.selectContext(csCallSite, recvObj, m);
            CSMethod csMethod = csManager.getCSMethod(ctx, m);

            workList.addEntry(
                    csManager.getCSVar(ctx, m.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            // calculate points-to relationship
            if (!callGraph.getCalleesOf(csCallSite).contains(csMethod)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod));
                addReachable(csMethod);

                // parameters and arguments
                for (int i = 0; i < m.getParamCount(); i++) {
                    CSVar a = csManager.getCSVar(csCallSite.getContext(), invoke.getInvokeExp().getArg(i));
                    CSVar p = csManager.getCSVar(ctx, m.getIR().getParam(i));
                    addPFGEdge(a, p);
                }

                // return values
                if (invoke.getLValue() != null)
                    m.getIR().getReturnVars().forEach(ret ->
                            addPFGEdge(csManager.getCSVar(ctx, ret),
                                    csManager.getCSVar(csCallSite.getContext(), invoke.getLValue())));
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
