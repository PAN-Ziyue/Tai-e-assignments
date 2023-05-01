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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    public Queue<Node> workList;    // change worklist to public

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        SetQueue<Node> entries = new SetQueue<>();
        icfg.entryMethods().forEach(method -> entries.add(icfg.getEntryOf(method)));

        for (Node node : icfg) {
            if (entries.contains(node))
                result.setOutFact(node, analysis.newBoundaryFact(node));
            else
                result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // initialization
        workList = new SetQueue<>();
        workList.addAll(icfg.getNodes());
        icfg.entryMethods().forEach(method -> workList.remove(icfg.getEntryOf(method)));

        while (!workList.isEmpty()) {
            // retrieve one element
            Node b = workList.poll();

            // compute in facts
            Fact tmp = analysis.newInitialFact();
            for (Node pred : icfg.getPredsOf(b)) {
                icfg.getInEdgesOf(b).forEach(edge -> {
                    if (edge.getSource() == pred) {
                        Fact edgeFact = analysis.transferEdge(edge, result.getOutFact(pred));
                        analysis.meetInto(edgeFact, tmp);
                    }
                });
            }

            result.setInFact(b, tmp);

            // manage successors
            if (analysis.transferNode(b, result.getInFact(b), result.getOutFact(b)))
                workList.addAll(icfg.getSuccsOf(b));
        }
    }
}
