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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Set;

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
        CPFact cpFact = new CPFact();
        // 处理变量范围
        List<Var> params = cfg.getIR().getParams();
        for (Var var : params){
            if (canHoldInt(var)){
                // 为什么初始化为NAC
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        // 会不会存在key不相等的问题
        Set<Var> vars = fact.keySet();
        for (Var var : vars){
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        if (v1.isUndef() || v2.isUndef()){
            return v1.isUndef() ? v2 : v1;
        }
        if (v1.isConstant() && v2.isConstant()){
            return v1.getConstant() == v2.getConstant() ?
                    Value.makeConstant(v1.getConstant()) :
                    Value.getNAC();
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt definitionStmt){
            LValue lValue = definitionStmt.getLValue();
            RValue rValue = definitionStmt.getRValue();
            if (lValue instanceof Var var && canHoldInt(var)){
                CPFact tmpFact = new CPFact();
                tmpFact.copyFrom(in);
                tmpFact.update(var, evaluate(rValue, in));
                return out.copyFrom(tmpFact);
            }
        }
        return out.copyFrom(in);
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
        if (exp instanceof IntLiteral intLiteral){
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof Var var){
            return in.get(var);
        }
        if (exp instanceof BinaryExp binaryExp){

            Var operand1 = binaryExp.getOperand1();
            Var operand2 = binaryExp.getOperand2();
            Value value1 = in.get(operand1);
            Value value2 = in.get(operand2);

            if (value1.isNAC() || value2.isNAC()){
                return Value.getNAC();
            }

            if (value1.isConstant() && value2.isConstant()){
                String operator = binaryExp.getOperator().toString();
                int c1 = value1.getConstant();
                int c2 = value2.getConstant();

                switch (operator){
                    case "+":
                        return Value.makeConstant(c1 + c2);
                    case "-":
                        return Value.makeConstant(c1 - c2);
                    case "*":
                        return Value.makeConstant(c1 * c2);
                    case "/":
                        return c2 == 0 ?
                                Value.getNAC() :
                                Value.makeConstant(c1 / c2);
                    case "==":
                        return c1 == c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case "!=":
                        return c1 != c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case "<":
                        return c1 < c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case ">":
                        return c1 > c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case "<=":
                        return c1 <= c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case ">=":
                        return c1 >= c2 ?
                                Value.makeConstant(1) :
                                Value.makeConstant(0);
                    case "<<":
                        return Value.makeConstant(c1 << c2);
                    case ">>":
                        return Value.makeConstant(c1 >> c2);
                    case ">>>":
                        return Value.makeConstant(c1 >>> c2);
                    case "|":
                        return Value.makeConstant(c1 | c2);
                    case "&":
                        return Value.makeConstant(c1 & c2);
                    case "^":
                        return Value.makeConstant(c1 ^ c2);
                    default:
                        return Value.getUndef();
                }
            }
        }
        return Value.getUndef();
    }
}
