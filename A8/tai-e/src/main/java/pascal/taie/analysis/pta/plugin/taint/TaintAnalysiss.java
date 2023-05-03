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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public final MultiMap<CSVar, Invoke> taintFlowGraph; // var -> callsite

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        taintFlowGraph = Maps.newMultiMap();
    }

    // process sources at each invoke statement
    public void processSources(Invoke invoke, Context callContext) {
        for (Source source : config.getSources()) {
            JMethod m = invoke.getMethodRef().resolve();

            // check taint source
            if (source.equals(new Source(m, m.getReturnType()))) {
                Obj taintObj = manager.makeTaint(invoke, source.type());
                Var taintVar = invoke.getLValue();
                if (taintObj != null && taintVar != null)
                    solver.addWorkList(
                            csManager.getCSVar(callContext, taintVar),
                            PointsToSetFactory.make(csManager.getCSObj(emptyContext, taintObj))
                    );
            }
        }
    }

    // taint transfer rules
    // generate new taint object and put the pts into the worklist
    public void transferTaint(JMethod method, CSVar base, CSCallSite callSite) {
        PointerAnalysisResult result = solver.getResult();

        // base-to-result
        if (base != null && callSite.getCallSite().getLValue() != null &&
                config.getTransfers().contains(new TaintTransfer(
                        method, TaintTransfer.BASE, TaintTransfer.RESULT, method.getReturnType()))) {

            result.getPointsToSet(base).forEach(csObj -> {
                if (manager.isTaint(csObj.getObject())) {
                    Invoke source = manager.getSourceCall(csObj.getObject());
                    Obj taintObj = manager.makeTaint(source, method.getReturnType());
                    Var taintVar = callSite.getCallSite().getLValue();
                    solver.addWorkList(
                            csManager.getCSVar(callSite.getContext(), taintVar),
                            PointsToSetFactory.make(csManager.getCSObj(emptyContext, taintObj))
                    );
                }
            });
        }

        // arg-to-base
        for (int i = 0; i < callSite.getCallSite().getInvokeExp().getArgCount(); i++) {
            if (base != null && config.getTransfers().contains(new TaintTransfer(
                    method, i, TaintTransfer.BASE, base.getType()))) {

                result.getPointsToSet(csManager.getCSVar(callSite.getContext(),
                        callSite.getCallSite().getInvokeExp().getArg(i))).forEach(csObj -> {
                    if (manager.isTaint(csObj.getObject())) {
                        Invoke source = manager.getSourceCall(csObj.getObject());
                        Obj taintObj = manager.makeTaint(source, base.getType());
                        solver.addWorkList(
                                csManager.getCSVar(callSite.getContext(), base.getVar()),
                                PointsToSetFactory.make(csManager.getCSObj(emptyContext, taintObj))
                        );
                    }
                });
            }
        }

        // arg-to-result
        for (int i = 0; i < callSite.getCallSite().getInvokeExp().getArgCount(); i++) {
            if (callSite.getCallSite().getLValue() != null && config.getTransfers().contains(new TaintTransfer(
                    method, i, TaintTransfer.RESULT, method.getReturnType()))) {

                result.getPointsToSet(csManager.getCSVar(callSite.getContext(),
                        callSite.getCallSite().getInvokeExp().getArg(i))).forEach(csObj -> {
                    if (manager.isTaint(csObj.getObject())) {
                        Invoke source = manager.getSourceCall(csObj.getObject());
                        Obj taintObj = manager.makeTaint(source, method.getReturnType());
                        Var taintVar = callSite.getCallSite().getLValue();
                        solver.addWorkList(
                                csManager.getCSVar(callSite.getContext(), taintVar),
                                PointsToSetFactory.make(csManager.getCSObj(emptyContext, taintObj))
                        );
                    }
                });
            }
        }
    }


    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        result.getCSCallGraph().reachableMethods().forEach(csMethod -> {
            result.getCSCallGraph().getCallersOf(csMethod).forEach(csCallSite -> {
                JMethod callee = csMethod.getMethod();
                Invoke callSite = csCallSite.getCallSite();

                for (int i = 0; i < callee.getParamCount(); i++) {
                    Var arg = callSite.getInvokeExp().getArg(i);

                    if (config.getSinks().contains(new Sink(callee, i))) {
                        for (Obj obj : result.getPointsToSet(arg)) {
                            if (manager.isTaint(obj))
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, i));
                        }
                    }
                }
            });
        });

        return taintFlows;
    }
}
