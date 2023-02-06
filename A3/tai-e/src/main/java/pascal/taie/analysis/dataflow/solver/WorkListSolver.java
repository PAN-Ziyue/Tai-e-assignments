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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashSet;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // initialization
        HashSet<Node> worklist = new HashSet<>();
        for (Node n : cfg)
            if (n != cfg.getEntry())    // exempt entry from the worklist
                worklist.add(n);

        while (!worklist.isEmpty()) {
            // retrieve one element
            Node b = worklist.iterator().next();
            worklist.remove(b);

            // compute in facts
            Fact tmp = analysis.newInitialFact();
            for (Node s : cfg.getPredsOf(b))
                analysis.meetInto(result.getOutFact(s), tmp);
            result.setInFact(b, tmp);

            // manage successors
            if (analysis.transferNode(b, result.getInFact(b), result.getOutFact(b)))
                worklist.addAll(cfg.getSuccsOf(b));
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // initialization
        HashSet<Node> worklist = new HashSet<>();
        for (Node n : cfg)
            if (n != cfg.getExit())    // exempt exit from the worklist
                worklist.add(n);

        while (!worklist.isEmpty()) {
            // retrieve one element
            Node b = worklist.iterator().next();
            worklist.remove(b);

            // compute in facts
            Fact tmp = analysis.newInitialFact();
            for (Node s : cfg.getSuccsOf(b))
                analysis.meetInto(result.getInFact(s), tmp);
            result.setOutFact(b, tmp);

            // manage successors
            if (analysis.transferNode(b, result.getInFact(b), result.getOutFact(b)))
                worklist.addAll(cfg.getPredsOf(b));
        }
    }
}
