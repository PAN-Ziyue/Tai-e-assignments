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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        HashSet<JMethod> workList = new HashSet<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod method = workList.iterator().next();
            workList.remove(method);

            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);

                callGraph.callSitesIn(method).forEach(callSite -> {
                    for (JMethod targetMethod : resolve(callSite)) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, targetMethod));
                        workList.add(targetMethod);
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> targets = new HashSet<>();
        JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                targets.add(declaringClass.getDeclaredMethod(subsignature));
            }
            case SPECIAL -> {
                JMethod dispatchMethod = dispatch(declaringClass, subsignature);
                if (dispatchMethod != null)
                    targets.add(dispatchMethod);
            }
            case VIRTUAL, INTERFACE -> {
                JMethod dispatchMethod = dispatch(declaringClass, subsignature);
                if (dispatchMethod != null)
                    targets.add(dispatchMethod);
                for (JClass c : hierarchy.getDirectSubclassesOf(declaringClass)) {
                    dispatchMethod = dispatch(c, subsignature);
                    if (dispatchMethod != null)
                        targets.add(dispatchMethod);
                }
                for (JClass c : hierarchy.getDirectSubinterfacesOf(declaringClass)) {
                    dispatchMethod = dispatch(c, subsignature);
                    if (dispatchMethod != null)
                        targets.add(dispatchMethod);
                }
                for (JClass c : hierarchy.getDirectImplementorsOf(declaringClass)) {
                    dispatchMethod = dispatch(c, subsignature);
                    if (dispatchMethod != null)
                        targets.add(dispatchMethod);
                }
            }
        }

        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        for (JMethod m : jclass.getDeclaredMethods()) {
            if (m.getSubsignature().equals(subsignature) && !m.isAbstract()) {
                return m;
            }
        }

        if (jclass.getSuperClass() != null)
            return dispatch(jclass.getSuperClass(), subsignature);
        else
            return null;
    }
}
