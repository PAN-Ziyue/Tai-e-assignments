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
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;
    private HashMap<Var, HashSet<Var>> aliasMap;

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
        
        pta.getVars().forEach(var -> {
            System.out.print(var.getName());
            System.out.print(": ");
            pta.getPointsToSet(var).forEach(System.out::print);
            System.out.println();
        });

        System.out.println("haha");
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
        // TODO - finish me
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);

        return !old.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
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

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact res = out.copy();

        if (edge.getSource() instanceof Invoke invoke) {
            if (invoke.getResult() != null)
                res.remove(invoke.getResult());
        }

        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
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
        // TODO - finish me
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

    // wrapper evaluate to handle field and array access
    private Value evaluate(Exp exp, CPFact in) {
        Value v = Value.getUndef();
        if (exp instanceof InstanceFieldAccess access) {
            Var base = access.getBase();
            for (Var aliasVar : aliasMap.get(base)) {
                for (StoreField field : aliasVar.getStoreFields()) {
                    v = cp.meetValue(v, ConstantPropagation.evaluate(field.getRValue(), in));
                }
            }
        } else if (exp instanceof StaticFieldAccess access) {
            for (Stmt stmt : icfg.getNodes()) {
                if (stmt instanceof StoreField field &&
                        field.isStatic() && field.getFieldRef() == access.getFieldRef()) {
                    v = cp.meetValue(v, ConstantPropagation.evaluate(field.getRValue(), in));
                }
            }
        } else if (exp instanceof ArrayAccess access) {
            Var base = access.getBase();
            Value idx = ConstantPropagation.evaluate(access.getIndex(), in);
            for (Var aliasVar : aliasMap.get(base)) {
                for (StoreArray storeArray : aliasVar.getStoreArrays()) {
                    ArrayAccess array = storeArray.getArrayAccess();
                    Value aliasIdx = ConstantPropagation.evaluate(array.getIndex(), in);

                    if ((idx.isNAC() && !aliasIdx.isUndef()) ||
                            (idx.isConstant() && aliasIdx.isNAC()) ||
                            (idx.isConstant() && aliasIdx.isConstant() && idx.getConstant() == aliasIdx.getConstant())
                    ) {
                        v = cp.meetValue(v, ConstantPropagation.evaluate(storeArray.getRValue(), in));
                    }
                }
            }
        } else {
            v = ConstantPropagation.evaluate(exp, in);
        }
        return v;
    }
}
