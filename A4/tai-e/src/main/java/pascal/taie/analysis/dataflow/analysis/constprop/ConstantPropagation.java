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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();

        // initialize integer parameters to NAC
        for (Var v : cfg.getIR().getParams())
            if (canHoldInt(v))
                fact.update(v, Value.getNAC());

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var k : fact.keySet())
            target.update(k, meetValue(target.get(k), fact.get(k)));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        Value v;
        if (v1.isNAC() || v2.isNAC())
            v = Value.getNAC();
        else if (v1.isUndef())
            v = v2;
        else if (v2.isUndef())
            v = v1;
        else if (v1.getConstant() == v2.getConstant())
            v = Value.makeConstant(v1.getConstant());
        else
            v = Value.getNAC();
        return v;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);

        if (stmt instanceof DefinitionStmt<?, ?> def) {
            if (def.getLValue() instanceof Var var && canHoldInt(var)) {
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
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        Value v;
        if (exp instanceof Var var && canHoldInt(var)) {
            v = in.get(var);
        } else if (exp instanceof IntLiteral literal) {
            v = Value.makeConstant(literal.getValue());
        } else if (exp instanceof BinaryExp bin) {
            Value yVal = in.get(bin.getOperand1()), zVal = in.get(bin.getOperand2());
            if (yVal.isConstant() && zVal.isConstant()) {
                int res = 0, y = yVal.getConstant(), z = zVal.getConstant();
                boolean divZero = false;

                if (bin.getOperator() instanceof ArithmeticExp.Op op) {
                    switch (op) {
                        case ADD -> res = y + z;
                        case SUB -> res = y - z;
                        case MUL -> res = y * z;
                        case DIV -> {
                            if (z == 0) divZero = true;
                            else res = y / z;
                        }
                        case REM -> {
                            if (z == 0) divZero = true;
                            else res = y % z;
                        }
                    }
                } else if (bin.getOperator() instanceof BitwiseExp.Op op) {
                    switch (op) {
                        case OR -> res = y | z;
                        case AND -> res = y & z;
                        case XOR -> res = y ^ z;
                    }
                } else if (bin.getOperator() instanceof ConditionExp.Op op) {
                    boolean cond = false;
                    switch (op) {
                        case EQ -> cond = y == z;
                        case NE -> cond = y != z;
                        case LT -> cond = y < z;
                        case GT -> cond = y > z;
                        case LE -> cond = y <= z;
                        case GE -> cond = y >= z;
                    }
                    res = cond ? 1 : 0;
                } else if (bin.getOperator() instanceof ShiftExp.Op op) {
                    switch (op) {
                        case SHL -> res = y << z;
                        case SHR -> res = y >> z;
                        case USHR -> res = y >>> z;
                    }
                }

                v = divZero ? Value.getUndef() : Value.makeConstant(res);
            } else if (yVal.isNAC()) {
                BinaryExp.Op op = bin.getOperator();
                if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) && zVal.isConstant() && zVal.getConstant() == 0)
                    v = Value.getUndef();   // if div by zero, result will be Undef even if y is NAC
                else
                    v = Value.getNAC();
            } else if (zVal.isNAC()) {
                v = Value.getNAC();
            } else {
                v = Value.getUndef();
            }
        } else {
            v = Value.getNAC();
        }
        return v;
    }
}