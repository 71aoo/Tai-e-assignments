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
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Set<Stmt> reachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Stmt entry = cfg.getEntry();

        dfs(entry, cfg, constants, liveVars, deadCode, reachable);
        
        // unreachable
        for (Stmt s : cfg){
            if (!reachable.contains(s)){
                deadCode.add(s);
            }
        }
        return deadCode;
    }

    public void dfs(Stmt stmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants,
                    DataflowResult<Stmt, SetFact<Var>> liveVars, Set<Stmt> deadCode, Set<Stmt> reachableCode){
        // 已经遍历过了
        if (!reachableCode.add(stmt) && !deadCode.contains(stmt)){
            return;
        }
        // 检测
        doCheck(stmt, cfg, constants, liveVars, deadCode);
        // 递归
        for (Stmt s : cfg.getSuccsOf(stmt)){
            dfs(s, cfg, constants, liveVars, deadCode, reachableCode);
        }

    }

    public void doCheck(Stmt stmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants,
                        DataflowResult<Stmt, SetFact<Var>> liveVars, Set<Stmt> deadCode){
        // if
        if (stmt instanceof If ifStmt){
            ConditionExp condition = ifStmt.getCondition();
            // CPFact inFact = constants.getInFact(stmt);
            CPFact outFact = constants.getOutFact(stmt);
            Value evaluate = ConstantPropagation.evaluate(condition, outFact);
            Edge.Kind deadEdgeKind = null;
            // always false
            if (evaluate.isConstant() && evaluate.getConstant() == 0){
                deadEdgeKind = Edge.Kind.IF_TRUE;
            }
            // always ture
            if (evaluate.isConstant() && evaluate.getConstant() != 0){
                deadEdgeKind = Edge.Kind.IF_FALSE;
            }
            if (deadEdgeKind != null){
                Set<Edge<Stmt>> outEdgesOf = cfg.getOutEdgesOf(stmt);
                for (Edge<Stmt> edge : outEdgesOf){
                    if (edge.getKind() == deadEdgeKind){
                        checkIfBranchDeadCode(edge.getTarget(), ifStmt, cfg, deadCode);
                    }
                }
            }
        }
        if (stmt instanceof AssignStmt assignStmt){
            SetFact<Var> outFact = liveVars.getOutFact(stmt);
            LValue lValue = assignStmt.getLValue();
            if (lValue instanceof Var lvar){
                if (!outFact.contains(lvar) && hasNoSideEffect(assignStmt.getRValue())){
                    deadCode.add(stmt);
                }
            }
        }
        // switch
        if (stmt instanceof SwitchStmt switchStmt){
            Var var = switchStmt.getVar();
            CPFact outFact = constants.getOutFact(stmt);
            Value value = outFact.get(var);
            if (value.isConstant()){
                List<Integer> caseValues = switchStmt.getCaseValues();
                Set<Edge<Stmt>> outEdgesOf = cfg.getOutEdgesOf(stmt);
                // case
                if (caseValues.contains(value.getConstant())){
                    for (Edge<Stmt> edge : outEdgesOf){
                        if ((edge.getKind() == Edge.Kind.SWITCH_CASE &&
                                edge.getCaseValue() != value.getConstant()) ||
                                edge.getKind() == Edge.Kind.SWITCH_DEFAULT){
                            checkSwitchBranchDeadCode(edge.getTarget(), switchStmt, cfg, deadCode);
                        }
                    }
                }else { // default
                    for (Edge<Stmt> edge : outEdgesOf){
                        if (edge.getKind() != Edge.Kind.SWITCH_DEFAULT){
                            checkSwitchBranchDeadCode(edge.getTarget(), switchStmt, cfg, deadCode);
                        }
                    }
                }
            }
        }
    }

    public void checkIfBranchDeadCode(Stmt stmt,If ifStmt, CFG<Stmt> cfg, Set<Stmt> deadCode){
        // 默认为 deadCode
        deadCode.add(stmt);
        for (Stmt pred : cfg.getPredsOf(stmt)){
            // 前驱不是 if 判断语句， 且不是 deadCode，则其可能是不是 deadCode
            if (pred != ifStmt && !deadCode.contains(pred)){
                deadCode.remove(stmt);
            }
        }
        checkBranchDeadCode(stmt, cfg, deadCode);
    }

    public void checkSwitchBranchDeadCode(Stmt stmt, SwitchStmt switchStmt, CFG<Stmt> cfg, Set<Stmt> deadCode){
        // 默认为 deadCode
        deadCode.add(stmt);
        for (Stmt pred : cfg.getPredsOf(stmt)){
            // 前驱不是switch判断语句， 且不是 deadCode，则其可能是不是 deadCode
            if (pred != switchStmt && !deadCode.contains(pred)){
                deadCode.remove(stmt);
            }
        }
        checkBranchDeadCode(stmt, cfg, deadCode);
    }

    /**
     * DFS 对分支 deadCode 进行检测
     * @param stmt
     * @param cfg
     * @param deadCode
     */
    public void checkBranchDeadCode(Stmt stmt, CFG<Stmt> cfg, Set<Stmt> deadCode){
        // 本身不是 deadCode， 其后驱更不可能是
        if (deadCode.contains(stmt)){
            for (Stmt succ : cfg.getSuccsOf(stmt)){
                if (!cfg.isExit(succ)){
                    // 默认为 deadCode
                    deadCode.add(succ);
                    // 前驱可达，则其亦可达
                    for (Stmt pred : cfg.getPredsOf(succ)){
                        if (!deadCode.contains(pred)){
                            deadCode.remove(succ);
                        }
                    }
                    checkBranchDeadCode(succ, cfg, deadCode);
                }
            }
        }
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
