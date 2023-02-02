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
        // TODO - finish me
        CPFact fact = new CPFact();

        for (Var v : cfg.getIR().getParams())
            fact.update(v, Value.getNAC());

//        CPFact fact = new CPFact();
//        for (Stmt s : cfg.getNodes()) {
//            if (s.getDef().isPresent() && s.getDef().get() instanceof Var v && canHoldInt(v))
//                fact.update(v, Value.getNAC());
//            for (RValue rv : s.getUses()) {
//                if (rv instanceof Var v && canHoldInt(v))
//                    fact.update(v, Value.getNAC());
//            }
//        }
//        return fact;
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var k : fact.keySet()) {
            target.update(k, meetValue(target.get(k), fact.get(k)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value v;
        if (v1.isNAC() || v2.isNAC())
            v = Value.getNAC();
        else if (v1.isUndef())
            v = v2;
        else if (v2.isUndef())
            v = v1;
        else {
            if (v1.getConstant() == v2.getConstant())
                v = Value.makeConstant(v1.getConstant());
            else
                v = Value.getNAC();
        }
        return v;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old = out.copy();
        out.clear();
        out.copyFrom(in);

        if (stmt instanceof DefinitionStmt<?, ?> def) {
            if (def.getLValue() instanceof Var var && canHoldInt(var)) {
                out.remove(var);

                if (def.getRValue() != null) {
                    Value eval = evaluate(def.getRValue(), in);
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
        // TODO - finish me
        Value v;
        if (exp instanceof Var var) {
            v = in.get(var);
        } else if (exp instanceof IntLiteral literal) {
            v = Value.makeConstant(literal.getValue());
        } else if (exp instanceof BinaryExp bin) {
            Var y = bin.getOperand1(), z = bin.getOperand2();
            if (in.get(y).isConstant() && in.get(z).isConstant()) {
                BinaryExp.Op op = bin.getOperator();
                int res = 0, int_y = in.get(y).getConstant(), int_z = in.get(z).getConstant();
                boolean div_zero = false;

                if (op instanceof ArithmeticExp.Op arithmetic) {
                    switch (arithmetic) {
                        case ADD -> res = int_y + int_z;
                        case SUB -> res = int_y - int_z;
                        case MUL -> res = int_y * int_z;
                        case DIV -> {
                            if (int_z == 0) div_zero = true;
                            else res = int_y / int_z;
                        }
                        case REM -> {
                            if (int_z == 0) div_zero = true;
                            else res = int_y % int_z;
                        }
                    }
                } else if (op instanceof BitwiseExp.Op bitwise) {
                    switch (bitwise) {
                        case OR -> res = int_y | int_z;
                        case AND -> res = int_y & int_z;
                        case XOR -> res = int_y ^ int_z;
                    }
                } else if (op instanceof ConditionExp.Op condition) {
                    boolean cond = false;
                    switch (condition) {
                        case EQ -> cond = int_y == int_z;
                        case NE -> cond = int_y != int_z;
                        case LT -> cond = int_y < int_z;
                        case GT -> cond = int_y > int_z;
                        case LE -> cond = int_y <= int_z;
                        case GE -> cond = int_y >= int_z;
                    }
                    res = cond ? 1 : 0;
                } else if (op instanceof ShiftExp.Op shift) {
                    switch (shift) {
                        case SHL -> res = int_y << int_z;
                        case SHR -> res = int_y >> int_z;
                        case USHR -> res = int_y >>> int_z;
                    }
                }

                v = div_zero ? Value.getUndef() : Value.makeConstant(res);
            } else if (in.get(y).isNAC() || in.get(z).isNAC()) {
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
