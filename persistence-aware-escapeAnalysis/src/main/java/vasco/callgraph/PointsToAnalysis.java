/**
 * Copyright (C) 2013 Rohan Padhye
 * 
 * This library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as 
 * published by the Free Software Foundation, either version 2.1 of the 
 * License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package vasco.callgraph;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Local;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.BytecodeOffsetTag;
import vasco.CallSite;
import vasco.Context;
import vasco.OldForwardInterProceduralAnalysis;
import vasco.ProgramRepresentation;
import vasco.soot.AbstractNullObj;
import vasco.soot.DefaultJimpleRepresentation;

/**
 * An inter-procedural analysis for constructing a context-sensitive call graph
 * on-the-fly.
 * 
 * <p>
 * This analysis uses the value-based context-sensitive inter-procedural
 * framework and was developed as an example instantiation of the framework.
 * </p>
 * 
 * <p>
 * The analysis uses {@link PointsToGraph} objects as data flow values, which in
 * turn abstracts heap locations using allocation sites.
 * <p>
 * 
 * <p>
 * <strong>Warning!</strong> The current implementation of this class uses the
 * old API (see {@link OldForwardInterProceduralAnalysis}) without separate
 * call/return flow functions. The developer is currently in the process of
 * migrating this implementation to the new API (see
 * {@link vasco.ForwardInterProceduralAnalysis ForwardInterProceduralAnalysis}).
 * </p>
 * 
 * @author Rohan Padhye
 */
public class PointsToAnalysis extends OldForwardInterProceduralAnalysis<SootMethod, Unit, PointsToGraph> {

	private static final SootMethod DUMMY_METHOD = new SootMethod("DUMMY_METHOD", Collections.EMPTY_LIST,
			Scene.v().getObjectType());

	/**
	 * A shared points-to graph that maintains information about objects reachable
	 * from static fields (modelled as fields of a dummy global variable).
	 * 
	 * <p>
	 * For static load/store statements, we union this points-to graph with the
	 * points-to graph in the flow function, perform the operation, and then
	 * separate stuff out again.
	 * </p>
	 */
	private PointsToGraph staticHeap;

	static Map<Integer, Set<Integer>> escapingPutField = new HashMap<>();
	static Map<Integer, Set<Integer>> escapingRhs = new HashMap<>();
	static HashSet<SootMethod> libmethod = new HashSet<>();
	static HashSet<Integer> methodsWithReflection = new HashSet<>();
	public static HashSet<AnyNewExpr> summaryObject = new HashSet<>();
	static HashMap<Stmt, AnyNewExpr> summaryObjectMapping = new HashMap<>();

	/**
	 * A set of classes whose static initialisers have been processed.
	 */
	private Set<SootClass> clinitCalled;

	public Map<AnyNewExpr, String> bciMap;
	public Map<AnyNewExpr, BciContainer> bciMap2;
	public SootMethod threadStartMethod;
	public static HashMap<Integer, HashSet<Stmt>> pfc = new HashMap<>();

	// public Map<AnyNewExpr, String> exprToMethodMap;
	

	/**
	 * Constructs a new points-to analysis as a forward-flow inter-procedural
	 * analysis.
	 */
	public PointsToAnalysis() {
		super();

		// Play around with these flags
		this.freeResultsOnTheFly = true;
		// this.verbose = true;

		// No classes statically initialised yet
		this.clinitCalled = new HashSet<SootClass>();

		// Create a static points-to graph with a single "global" root object
		this.staticHeap = topValue();
		this.staticHeap.assignNew(PointsToGraph.GLOBAL_LOCAL, PointsToGraph.GLOBAL_SITE);

		this.bciMap = new HashMap<AnyNewExpr, String>();
		this.bciMap2 = new HashMap<AnyNewExpr, BciContainer>();

		this.threadStartMethod = Scene.v().getSootClass("java.lang.Thread").getMethodByNameUnsafe("start");

		assert (threadStartMethod != null);
	}

	/**
	 * Returns a points-to graph with the locals of main initialised to
	 * <tt>null</tt>, except the command-line arguments which are initialised to an
	 * array of strings.
	 */
	@Override
	public PointsToGraph boundaryValue(SootMethod entryPoint) {
		// For now we only support entry to the main method
		assert (entryPoint == Scene.v().getMainMethod());

		// Ok, start setting up entry value
		PointsToGraph entryValue = new PointsToGraph();

		// Locals of main... (only reference types)
		SootMethod mainMethod = Scene.v().getMainMethod();
		for (Local local : mainMethod.getActiveBody().getLocals()) {
			if (local.getType() instanceof RefLikeType) {
				entryValue.assign(local, null, false);
			}
		}

		// Command-line arguments to main...
		Local argsLocal = mainMethod.getActiveBody().getParameterLocal(0);

		entryValue.setFieldConstant(argsLocal, PointsToGraph.ARRAY_FIELD, PointsToGraph.STRING_CONST);

		return entryValue;
	}

	/**
	 * Returns a copy of the given points-to graph.
	 */
	@Override
	public PointsToGraph copy(PointsToGraph graph) {
		return new PointsToGraph(graph);
	}

	/**
	 * Performs operations on points-to graphs depending on the statement inside a
	 * CFG node.
	 */
	@Override
	protected PointsToGraph flowFunction(Context<SootMethod, Unit, PointsToGraph> context, Unit unit,
			PointsToGraph in) {

		// First set OUT to copy of IN (this is default for most statements).

		PointsToGraph out = new PointsToGraph(in);

		// This analysis is written assuming that units are statements (and not,
		// for example, basic blocks)
		assert (unit instanceof Stmt);
		Stmt stmt = (Stmt) unit;

		int bci = -1;
//		try {
		BytecodeOffsetTag bT = (BytecodeOffsetTag) unit.getTag("BytecodeOffsetTag");
		if (bT != null)
			bci = bT.getBytecodeOffset();
	
		

		String currentMethodSignature = getTrimmedByteCodeSignature(context.getMethod());
		int currentMethodIndex = this.methodIndices.get(currentMethodSignature);

		// SHASHIN

		if (isReflectedStatement(stmt)) {
			List<SootMethod> reflectionAffected = context.getMethod().getDeclaringClass().getMethods();
			for(SootMethod rm: reflectionAffected) {
				String sig = getTrimmedByteCodeSignature(rm);
				int index = this.methodIndices.size();
				//maintain an index for each unique method signature
				
				if(! this.methodIndices.containsKey(sig)) {
					this.methodIndices.put(sig, ++index);
				}

				PointsToAnalysis.methodsWithReflection.add(this.methodIndices.get(sig));
			}
			
			return out;
		}




		// What kind of statement?
		if (stmt instanceof DefinitionStmt) {
			// System.out.println(stmt);
			// Assignment of LHS to an RHS
			Value lhsOp = ((DefinitionStmt) stmt).getLeftOp();
			Value rhsOp = ((DefinitionStmt) stmt).getRightOp();
			// Invoke static initialisers if static members accessed
			// for the first time
			StaticFieldRef staticReference = null;
			if (lhsOp instanceof StaticFieldRef) {
				staticReference = ((StaticFieldRef) lhsOp);
			} else if (rhsOp instanceof StaticFieldRef) {
				staticReference = ((StaticFieldRef) rhsOp);
			}

			// Handle statement depending on type
			if (lhsOp.getType() instanceof RefLikeType) {
				// Both LHS and RHS are RefLikeType
				if (lhsOp instanceof InstanceFieldRef || lhsOp instanceof ArrayRef) {
					// SETFIELD
					Local lhs = (Local) (lhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) lhsOp).getBase()
							: ((ArrayRef) lhsOp).getBase());
					SootField field = lhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) lhsOp).getField()
							: PointsToGraph.ARRAY_FIELD;
					
					if (out.containsEscapeNode(lhs, field)) {
						if (!PointsToAnalysis.escapingPutField.containsKey(currentMethodIndex)) {
							PointsToAnalysis.escapingPutField.put(currentMethodIndex, new HashSet<>());
						}
						PointsToAnalysis.escapingPutField.get(currentMethodIndex).add(bci);
					}
					if(rhsOp instanceof Local && out.rhsContainsEscape((Local)rhsOp)) {
						if(!PointsToAnalysis.escapingRhs.containsKey(currentMethodIndex)) {
							PointsToAnalysis.escapingRhs.put(currentMethodIndex, new HashSet<>());
						}
						PointsToAnalysis.escapingRhs.get(currentMethodIndex).add(bci);
					}



					// RHS can be a local or constant (string, class, null)
					if (rhsOp instanceof Local) {
						Local rhs = (Local) rhsOp;
						out.setField(lhs, field, rhs);

					} else if (rhsOp instanceof Constant) {
						Constant rhs = (Constant) rhsOp;
						out.setFieldConstant(lhs, field, rhs);
					} else {
						throw new RuntimeException(rhsOp.toString());
					}
					// logic to store escaping putfield

					if (!pfc.containsKey(currentMethodIndex)) {
						pfc.put(currentMethodIndex, new HashSet<>());
					}
					pfc.get(currentMethodIndex).add(stmt);

				} else if (rhsOp instanceof InstanceFieldRef || rhsOp instanceof ArrayRef) {
					// GETFIELD
					Local rhs = (Local) (rhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) rhsOp).getBase()
							: ((ArrayRef) rhsOp).getBase());
					SootField field = rhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) rhsOp).getField()
							: PointsToGraph.ARRAY_FIELD;

					// LHS has to be local
					if (lhsOp instanceof Local) {
						Local lhs = (Local) lhsOp;

						out.getField(stmt, lhs, rhs, field);

					} else {
						throw new RuntimeException(lhsOp.toString());
					}

				} else if (rhsOp instanceof AnyNewExpr) {
					// NEW, NEWARRAY or NEWMULTIARRAY
					AnyNewExpr anyNewExpr = (AnyNewExpr) rhsOp;

					if (lhsOp instanceof Local) {
						Local lhs = (Local) lhsOp;
						out.assignNew(lhs, anyNewExpr);

						assert (bci != -1);
						assert (this.methodIndices.containsKey(currentMethodSignature));

						if (lhs.getName().charAt(0) != '$') {
							// special case - if the lhs is an actual local, subtract 3 from the bci to
							// obtain the bci for the new op
							bci = bci - 3;
						}

						this.bciMap2.put(anyNewExpr, new BciContainer(currentMethodIndex, bci));
						this.bciMap.put(anyNewExpr, currentMethodIndex + "-" + bci);
						

					} else {
						throw new RuntimeException(lhsOp.toString());
					}
				} else if (rhsOp instanceof InvokeExpr) {
					// STATICINVOKE, SPECIALINVOKE, VIRTUALINVOKE or INTERFACEINVOKE
					InvokeExpr expr = (InvokeExpr) rhsOp;
					// Handle method invocation!
					out = handleInvoke(context, stmt, expr, in);
					
					
					
					
				} else if (lhsOp instanceof StaticFieldRef) {
					// TODO: Static store

					// Get parameters
					SootField staticField = ((StaticFieldRef) lhsOp).getField();
					// Temporarily union locals and globals
					PointsToGraph tmp = topValue();
					tmp.union(out, staticHeap);
					// Store RHS into static field
					if (rhsOp instanceof Local) {
						Local rhsLocal = (Local) rhsOp;

						// summarise the heap reachable from rhsOp
						// tmp.summarizeTargetFields(rhsLocal);
						
						if(out.rhsContainsEscape(rhsLocal)) {
							if(!PointsToAnalysis.escapingRhs.containsKey(currentMethodIndex)) {
								PointsToAnalysis.escapingRhs.put(currentMethodIndex, new HashSet<>());
							}
							PointsToAnalysis.escapingRhs.get(currentMethodIndex).add(bci);
						}
						
						out.summarizeTargetFields(rhsLocal, true);
						
					} else if (rhsOp instanceof Constant) {
						Constant rhsConstant = (Constant) rhsOp;
						tmp.setFieldConstant(PointsToGraph.GLOBAL_LOCAL, staticField, rhsConstant);
					} else {
						throw new RuntimeException(rhsOp.toString());
					}
					// Now get rid of all locals, params, etc.
					Set<Local> locals = new HashSet<Local>(tmp.roots.keySet());
					for (Local local : locals) {
						// Everything except the GLOBAL must go!
						if (local != PointsToGraph.GLOBAL_LOCAL) {
							tmp.kill(local);
						}
					}
					// Global information is updated!
					staticHeap = tmp;

				} else if (rhsOp instanceof StaticFieldRef) {
					// TODO: Static load

					// Get parameters
					Local lhsLocal = (Local) lhsOp;
					SootField staticField = ((StaticFieldRef) rhsOp).getField();
					// Temporarily union locals and globals
					PointsToGraph tmp = topValue();
					tmp.union(out, staticHeap);
					// Load static field into LHS local
					// TODO: 1. assign summary to lhsLocal - static reads are all modeled as BOT
					tmp.assignPersistent(lhsLocal);
					// Now get rid of globals that we do not care about
					tmp.kill(PointsToGraph.GLOBAL_LOCAL);
					// Local information is updated!
					out = tmp;

				} else if (rhsOp instanceof CaughtExceptionRef) {
					Local lhs = (Local) lhsOp;
					out.assignPersistent(lhs);

				} else if (rhsOp instanceof IdentityRef) {
					// Ignore identities
				} else if (lhsOp instanceof Local) {
					// Assignment
					Local lhs = (Local) lhsOp;

					// RHS op is a local, constant or class cast
					if (rhsOp instanceof Local) {

						Local rhs = (Local) rhsOp;

						out.assign(lhs, rhs, false);

					} else if (rhsOp instanceof Constant) {

						Constant rhs = (Constant) rhsOp;
						out.assignConstant(lhs, rhs);
					} else if (rhsOp instanceof CastExpr) {
						Value op = ((CastExpr) rhsOp).getOp();
						if (op instanceof Local) {
							Local rhs = (Local) op;
							out.assign(lhs, rhs, false);
						} else if (op instanceof Constant) {
							Constant rhs = (Constant) op;
							out.assignConstant(lhs, rhs);
						} else {
							throw new RuntimeException(op.toString());
						}
					} else {
						throw new RuntimeException(rhsOp.toString());
					}
				} else {
					throw new RuntimeException(unit.toString());
				}
			} else if (rhsOp instanceof InvokeExpr) {
				// For non-reference types, only method invocations are important
				InvokeExpr expr = (InvokeExpr) rhsOp;
				// Handle method invocation!
				out = handleInvoke(context, stmt, expr, in);
			} else if (lhsOp instanceof InstanceFieldRef || lhsOp instanceof ArrayRef) {
				Local lhs = (Local) (lhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) lhsOp).getBase()
						: ((ArrayRef) lhsOp).getBase());
				SootField field = lhsOp instanceof InstanceFieldRef ? ((InstanceFieldRef) lhsOp).getField()
						: PointsToGraph.ARRAY_FIELD;

				// special case bytecode mismatch 
				if(context.getMethod().toString().contains("org.apache.lucene.store.BufferedIndexInput: byte readByte") && bci == 29) {
					bci -= 2;
				}
				
	
				if (out.containsEscapeNode(lhs, field)) {
					if (!PointsToAnalysis.escapingPutField.containsKey(currentMethodIndex)) {
						PointsToAnalysis.escapingPutField.put(currentMethodIndex, new HashSet<>());
					}
					PointsToAnalysis.escapingPutField.get(currentMethodIndex).add(bci);
				}
				if(rhsOp instanceof Local && out.rhsContainsEscape((Local)rhsOp)) {
					if(!PointsToAnalysis.escapingRhs.containsKey(currentMethodIndex)) {
						PointsToAnalysis.escapingRhs.put(currentMethodIndex, new HashSet<>());
					}
					PointsToAnalysis.escapingRhs.get(currentMethodIndex).add(bci);
				}
				if (!pfc.containsKey(currentMethodIndex)) {
					pfc.put(currentMethodIndex, new HashSet<>());
				}
				pfc.get(currentMethodIndex).add(stmt);

			}

		} else if (stmt instanceof InvokeStmt) {
			// INVOKE without a return
			InvokeExpr expr = stmt.getInvokeExpr();
			// Handle method invocation!
			out = handleInvoke(context, stmt, expr, in);

		} else if (stmt instanceof ReturnStmt) {
			// Returning a value (not return-void as those are of type ReturnVoidStmt)
			Value op = ((ReturnStmt) stmt).getOp();
			Local lhs = PointsToGraph.RETURN_LOCAL;
			// We only care about reference-type returns
			if (op.getType() instanceof RefLikeType) {

				// We can return a local or a constant
				if (op instanceof Local) {
					Local rhs = (Local) op;
					out.assign(lhs, rhs, false);
				} else if (op instanceof Constant) {
					Constant rhs = (Constant) op;
					out.assignConstant(lhs, rhs);

				} else {
					throw new RuntimeException(op.toString());
				}
			}
		}

		return out;

	}

	private boolean isReflectedStatement(Stmt stmt) {
		boolean isReflected = false;
		InvokeExpr ie = null;

		if (stmt instanceof DefinitionStmt) {
			// we only care to test if the RHS is an operation involving reflection
			Value rhsOp = ((DefinitionStmt) stmt).getRightOp();
			if (rhsOp instanceof InvokeExpr) {
				ie = (InvokeExpr) rhsOp;
			}

		} else if (stmt instanceof InvokeStmt) {
			ie = stmt.getInvokeExpr();
		}

		if (ie != null) {
			final Scene sc = Scene.v();
			SootMethodRef methodRef = ie.getMethodRef();
			switch (methodRef.getDeclaringClass().getName()) {
			case "java.lang.reflect.Method":
				if ("java.lang.Object invoke(java.lang.Object,java.lang.Object[])"
						.equals(methodRef.getSubSignature().getString())) {
					isReflected = true;
				}
				break;
			case "java.lang.reflect.Constructor":
				if ("java.lang.Object newInstance(java.lang.Object[])"
						.equals(methodRef.getSubSignature().getString())) {
//	                	System.out.println("this looks like a constructor newinstance!");
					isReflected = true;
				}
				break;
			default:
				break;

			}
		}
		return isReflected;
	}

	/**
	 * Computes the targets of an invoke expresssion purely based on the hierarchy
	 * of the receiver's type (not CHA) Use only when the receiver points to a
	 * summary node
	 * 
	 * @param receiver
	 * @param ie
	 * @return
	 */
	private SootMethod getTargetFromHierarchy(Local receiver, InvokeExpr ie) {
		SootMethod target = null;

		assert (receiver.getType() instanceof RefType);
		SootClass receiverType = ((RefType) receiver.getType()).getSootClass();

		String invokedMethodSubSig = ie.getMethod().getSubSignature();

		SootClass clazz = receiverType;
		do {
			if (clazz.declaresMethod(invokedMethodSubSig)) {
				target = clazz.getMethod(invokedMethodSubSig);
			} else if (clazz.hasSuperclass()) {
				clazz = clazz.getSuperclass();
			} else {
				clazz = null;
			}
		} while (clazz != null);

		return target;
	}

	/**
	 * Computes the targets of an invoke expression using a given points-to graph.
	 * 
	 * <p>
	 * For static invocations, there is only target. For instance method
	 * invocations, the targets depend on the type of receiver objects pointed-to by
	 * the instance variable whose method is being invoked.
	 * </p>
	 * 
	 * <p>
	 * If the instance variable points to a summary node, then the returned value is
	 * <tt>null</tt> signifying a <em>default</em> call-site.
	 * </p>
	 */
	static SootMethod thread_start = null;

	private Set<SootMethod> getTargets(SootMethod callerMethod, Stmt callStmt, InvokeExpr ie, PointsToGraph ptg) {
		Set<SootMethod> targets = new HashSet<SootMethod>();
		SootMethod invokedMethod = ie.getMethod();
		String subsignature = invokedMethod.getSubSignature();

		// Static and special invocations refer to the target method directly
		if (ie instanceof StaticInvokeExpr || ie instanceof SpecialInvokeExpr) {
			targets.add(invokedMethod);
			return targets;
		} else {
			assert (ie instanceof InterfaceInvokeExpr || ie instanceof VirtualInvokeExpr);
			// Get the receiver
			Local receiver = (Local) ((InstanceInvokeExpr) ie).getBase();
			// Get what objects the receiver points-to
			Set<AnyNewExpr> heapNodes = ptg.getTargets(receiver);

			/*
			 * TODO: if heapNodes contains a SUMMARY_NODE, then the callsite is summarised
			 * this is unsound, since it leads to NO methods being analysed at the callsite
			 * proposal : when a callsite is going to be summarised, fall back to CHA to
			 * resolve the targets
			 */

			boolean containsPersistent = heapNodes != null && heapNodes.contains(PointsToGraph.PERSISTENT_NODE);
			boolean containsEscape = heapNodes != null && heapNodes.contains(PointsToGraph.ESCAPE_NODE);
			boolean containsSummary = false;
			if(heapNodes != null) {
				for(AnyNewExpr node: heapNodes) {
					if(summaryObject.contains(node)) {
						containsSummary = true;
						break;
					}
				}
			}
			
			boolean containsSingletonNull = heapNodes != null && heapNodes.size() == 1
					&& heapNodes.contains(PointsToGraph.nullObj);

			if (containsSingletonNull || containsPersistent || containsEscape || containsSummary) {
				// TODO: if a thread.start() invocation has a BOT receiver, then it will never
				// get resolved thanks to this guard
				if (receiver.getType() instanceof RefType) {

					CallGraph cg = Scene.v().getCallGraph();
					Iterator<Edge> targetEdges = cg.edgesOutOf((Unit) callStmt);
					while (targetEdges.hasNext()) {
						SootMethod t = targetEdges.next().tgt();
						targets.add(t);
					}

					if (targets.size() == 1 && targets.iterator().next().equals(this.threadStartMethod)) {
						System.err.println("to short - thread.start: " + ie.toString());
					}

					if (!targets.isEmpty())
						return targets;
					else
						return null;
				}
			}

			if (heapNodes != null) {
				// For each object, find the invoked method for the declared type
				for (AnyNewExpr heapNode : heapNodes) {
					if (heapNode instanceof AbstractNullObj)
						continue;

					if (heapNode == PointsToGraph.PERSISTENT_NODE || heapNode == PointsToGraph.ESCAPE_NODE || summaryObject.contains(heapNode)) {
						// If even one pointee is a summary node, then this is a default site
						return null;
					} else if (heapNode instanceof NewArrayExpr) {
						// Probably getClass() or something like that on an array
						return null;
					}
					// Find the top-most class that declares a method with the given
					// signature and add it to the resulting targets
					SootClass sootClass = ((RefType) heapNode.getType()).getSootClass();

					// make a copy of the original receiver's sootClass
					SootClass receiverClass = sootClass;
					do {
						if (sootClass.declaresMethod(subsignature)) {
							// if sootClass == Thread && subsignature == "void start()", then
							// targets.add(receiverClass.getMethod("void run()")
							// this will basically inline the start-run sequence
							String className = sootClass.getName();
							if (thread_start == null && className.equals("java.lang.Thread")
									&& subsignature.equals("void start()")) {
								thread_start = invokedMethod;
							}
							if (thread_start == invokedMethod) {
								SootMethod threadRunMethod = receiverClass.getMethod("void run()");
								// getMethod will throw a RuntimeException if method doesn't exist - but that is
								// fine, the method is supposed to be defined
								System.out.println("short-circuited thread start with run for " + ie.toString()
										+ " caller method " + callerMethod.toString());
								targets.add(threadRunMethod);
							} else {
								// leave the original code alone
								targets.add(sootClass.getMethod(subsignature));
							}
							break;
						} else if (sootClass.hasSuperclass()) {
							sootClass = sootClass.getSuperclass();
						} else {
							sootClass = null;
						}
					} while (sootClass != null);
				}
			}
			if (targets.isEmpty()) {
				// System.err.println("Warning! Null call at: " + callStmt+ " in ");
				return null;
			}

			return targets;
		}
	}

	private Set<SootMethod> getDummyTarget() {
		Set<SootMethod> targets = new HashSet<SootMethod>();
		targets.add(DUMMY_METHOD);
		return targets;
	}

	/**
	 * Handles a call site by resolving the targets of the method invocation.
	 * 
	 * The resultant flow is the union of the exit flows of all the analysed
	 * callees. If the method returns a reference-like value, this is also taken
	 * into account.
	 */

	protected PointsToGraph handleInvoke(Context<SootMethod, Unit, PointsToGraph> callerContext, Stmt callStmt,
			InvokeExpr ie, PointsToGraph in) {

		// Get the caller method
		SootMethod callerMethod = callerContext.getMethod();

		// Initialise the final result as TOP first
		PointsToGraph resultFlow = topValue();

		// If this statement is an assignment to an object, then set LHS for
		// RETURN values.
		Local lhs = null;
		Value lhsOp = null;
		if (callStmt instanceof AssignStmt) {
			lhsOp = ((AssignStmt) callStmt).getLeftOp();
			if (lhsOp.getType() instanceof RefLikeType) {
				lhs = (Local) lhsOp;
			}
		}
		Set<SootMethod> targets = getTargets(callerMethod, callStmt, ie, in);

		if (targets != null) {

			BytecodeOffsetTag bT = (BytecodeOffsetTag) ((Unit) callStmt).getTag("BytecodeOffsetTag");
			assert (bT != null && bT.getBytecodeOffset() >= 0);
			// 1. check if the caller method already has an index
			String sig = getTrimmedByteCodeSignature(callerMethod);
			// the caller method HAS to have a method index already
			assert (this.methodIndices.containsKey(sig));
			Set<SootClass> receiversForCall = new HashSet<SootClass>();
			Map<Integer, Set<SootClass>> receiverInfo = this.callsiteReceiverReference.getOrDefault(callerMethod,
					new HashMap<Integer, Set<SootClass>>());
			for (SootMethod target : targets) {

				SootClass receiverClass = target.getDeclaringClass();
				if (receiverClass.getPackageName().startsWith("java.security")
						|| receiverClass.getPackageName().startsWith("javax.crypto")
						|| !receiverClass.isJavaLibraryClass()) {
					int classIndex;
					if (!this.sootClassIndices.containsKey(receiverClass)) {
						classIndex = this.sootClassIndices.size() + 1;
						this.sootClassIndices.put(receiverClass, classIndex);
					} else {
						// we don't really need the classIndex right now
						classIndex = this.sootClassIndices.get(receiverClass);
					}

					receiversForCall.add(receiverClass);
				}
			}
			
			if(bT!=null) {
				receiverInfo.put(bT.getBytecodeOffset(), receiversForCall);
				this.callsiteReceiverReference.put(callerMethod, receiverInfo);
			}
			
		}



		// If "targets" is null, that means the invoking instance was SUMMARY
		// So we use the DUMMY METHOD (which is a method with no body)
		if (targets == null) {
			targets = getDummyTarget();
			this.contextTransitions
					.addTransition(new CallSite<SootMethod, Unit, PointsToGraph>(callerContext, callStmt), null);
			if (verbose) {
				System.out.println("[DEF] X" + callerContext + " -> DEFAULT " + ie.getMethod());
			}
		}
		
		
		
		// Make calls for all target methods
		// if(targets.size() > 0) this.immediatePrevContextAnalysed = true;
		for (SootMethod calledMethod : targets) {

			
			boolean treatAsOpaque = false;
			if (!calledMethod.equals(DUMMY_METHOD)) {
				// treat as opaque all library methods, and methods in the soot.* package
				treatAsOpaque = calledMethod.isJavaLibraryMethod()
						|| methodsOverInvocationThreshold.contains(calledMethod)
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("soot.")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("scala.collection")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("scala.jdk")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("scala.math")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("scala.util")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.jfree");


				if (calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.lucene")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.xalan")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.avalon")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.xerces")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.batik")
						|| calledMethod.getDeclaringClass().getPackageName().startsWith("org.apache.fop"))
					//  || calledMethod.getDeclaringClass().getPackageName().startsWith("javax.crypto")
					//  || calledMethod.getDeclaringClass().getPackageName().startsWith("java.security")
					//  || calledMethod.getDeclaringClass().getPackageName().startsWith("com.sun.tools.javac"))
					treatAsOpaque = false;
				
				

				// EXCEPT ReflectiveCallsWrapper
				treatAsOpaque = treatAsOpaque && !calledMethod.getDeclaringClass()
						.equals(Scene.v().getSootClass("soot.rtlib.tamiflex.ReflectiveCallsWrapper"));

				// include all methods that will be partially analysed
				treatAsOpaque = treatAsOpaque || this.partiallyAnalysedMethods.contains(calledMethod);
				if (this.partiallyAnalysedMethods.contains(calledMethod))
					System.err.println("summarising potential partially analysed method " + calledMethod);
			}

			// The call-edge is obtained by assign para meters and THIS, and killing
			// caller's locals

			PointsToGraph callEdge = copy(in);
			if (!treatAsOpaque && calledMethod.hasActiveBody()) {

				// We need to maintain a set of locals not to kill (in case the call is
				// recursive)
				Set<Local> doNotKill = new HashSet<Local>();

				// Initialise sticky parameter
				callEdge.assign(PointsToGraph.STICKY_LOCAL, null, false);
				doNotKill.add(PointsToGraph.STICKY_LOCAL);

				// Assign this...
				if (ie instanceof InstanceInvokeExpr) {
					Local receiver = (Local) ((InstanceInvokeExpr) ie).getBase();
					Local thisLocal = calledMethod.getActiveBody().getThisLocal();
					callEdge.assign(thisLocal, receiver, false);
					doNotKill.add(thisLocal);
					// Sticky it!
					callEdge.assignSticky(PointsToGraph.STICKY_LOCAL, thisLocal);
				}

				// Assign parameters...
				for (int i = 0; i < calledMethod.getParameterCount(); i++) {
					// Only for reference-like parameters
					if (calledMethod.getParameterType(i) instanceof RefLikeType) {
						Local parameter = calledMethod.getActiveBody().getParameterLocal(i);
						Value argValue = ie.getArg(i);

						// The argument can be a constant or local, so handle accordingly
						if (argValue instanceof Local) {

							Local argLocal = (Local) argValue;
							callEdge.assign(parameter, argLocal, true);
							doNotKill.add(parameter);

							// Sticky it!
							callEdge.assignSticky(PointsToGraph.STICKY_LOCAL, argLocal);
						} else if (argValue instanceof Constant) {
							Constant argConstant = (Constant) argValue;
							callEdge.assignConstant(parameter, argConstant);
							doNotKill.add(parameter);
							// No need to sticky constants as caller does not store them anyway
						} else {
							throw new RuntimeException(argValue.toString());
						}
					}
				}

				// Kill caller data...
				for (Local callerLocal : callerMethod.getActiveBody().getLocals()) {
					if (doNotKill.contains(callerLocal) == false)
						callEdge.kill(callerLocal);
				}

				// There should be no "return local", but we kill it anyway (just in case)
				callEdge.kill(PointsToGraph.RETURN_LOCAL);

				// Create callee locals..
				for (Local calleeLocal : calledMethod.getActiveBody().getLocals()) {
					if (calleeLocal.getType() instanceof RefLikeType && doNotKill.contains(calleeLocal) == false) {
						callEdge.assign(calleeLocal, null, false);
					}
				}
			}

			// The intra-procedural edge is the IN value minus the objects from the call
			// edge
			PointsToGraph intraEdge = copy(in);
			if (lhs != null) {
				// Oh, and remove the LHS targets too
				intraEdge.assign(lhs, null, false);
			}
			// intraEdge.subtractHeap(callEdge);

			// Value at the start of the called procedure is
			// whatever went through the call edge
			PointsToGraph entryFlow = callEdge;


			// Make the call to this method!! (in case of body-less methods, no change)

			PointsToGraph exitFlow = (!treatAsOpaque && calledMethod.hasActiveBody()) ?
//					processCall(callerContext, callStmt, calledMethod, entryFlow) : entryFlow;
					processCallContextInsensitive(callerContext, callStmt, calledMethod, entryFlow) : entryFlow;

			

			if (exitFlow != null) {

				// Propagate stuff from called procedure's exit to the caller's return-site
				PointsToGraph returnEdge = copy(exitFlow);

			
				if (!treatAsOpaque && calledMethod.hasActiveBody()) {
					// Kill all the called method's locals. That's right.
					for (Local calleeLocal : calledMethod.getActiveBody().getLocals()) {
						returnEdge.kill(calleeLocal);
					}
					// Remove the stickies (so not to interfere with stickies in the intra-edge)
					// but do not collect unreachable nodes

					returnEdge.killWithoutGC(PointsToGraph.STICKY_LOCAL);
				}

				// Let's unite the intra-edge with the return edge

				PointsToGraph callOut = topValue();
				callOut.union(intraEdge, returnEdge);

				if (lhs != null) {
					callOut.roots.put(lhs, returnEdge.roots.get(PointsToGraph.RETURN_LOCAL));
				}
				
				// Now we are only left with the return value, if any
				if (!treatAsOpaque && calledMethod.hasActiveBody()) {
					
				}else { 
				
				
					
					SootMethod lib = callStmt.getInvokeExpr().getMethod();
					libmethod.add(lib);
					
					HashSet<AnyNewExpr> absSummarize = new HashSet<>();
					
//					handleLibraryCall1(callStmt, callOut, lhs);
					if(ie instanceof InterfaceInvokeExpr || ie instanceof VirtualInvokeExpr) {
						Local receiver = (Local) ((InstanceInvokeExpr) ie).getBase();
						if(CallGraphTransformer.safeMethod.contains(lib.toString())) {
							if(!CallGraphTransformer.safeArgMethod.contains(lib.toString())) {
								absSummarize.addAll(callOut.getTargets(receiver));
							}
						}else {
							callOut.summarizeTargetFields(receiver, false);
						}
						
					}
					
					for (int i = 0; i < ie.getMethod().getParameterCount(); i++) {
						
						// Only for reference-like parameters
					
						if (ie.getMethod().getParameterType(i) instanceof RefLikeType) {
							Value argValue = ie.getArg(i);
							// Summarize if the argument is local (i.e. not a constant)
							if (argValue instanceof Local) {
								Local argLocal = (Local) argValue;
								if(CallGraphTransformer.safeMethod.contains(lib.toString())) {
									if(!CallGraphTransformer.safeArgMethod.contains(lib.toString())) {
										absSummarize.addAll(callOut.getTargets(argLocal));
									}
								}else {
									callOut.summarizeTargetFields(argLocal, false);
								}
							}
						}
					}
					
					AnyNewExpr splObject;
					if(summaryObjectMapping.containsKey(callStmt)) {
						splObject = summaryObjectMapping.get(callStmt);
					}else {
//						splObject = new JNewExpr(null);
						splObject = PointsToGraph.SUMMARY_NODE; 
						summaryObjectMapping.put(callStmt, splObject);
					}
					
					
					if(CallGraphTransformer.safeMethod.contains(lib.toString())) {
						
						summaryObject.add(splObject);
						callOut.newNode(splObject, 0, new HashSet<>(), null);
						
						HashSet<AnyNewExpr> v = new HashSet<>();
						for(AnyNewExpr node: absSummarize) {
							callOut.newNode(node, 3, v, splObject);
						}
						v = new HashSet<>();
						
						for(AnyNewExpr key: callOut.heap.keySet()) {
							if(summaryObject.contains(key) && callOut.heap.get(key).get(PointsToGraph.SUMMARY_FIELD).contains(PointsToGraph.ESCAPE_NODE)
									&& !callOut.heap.get(key).containsKey(PointsToGraph.ESCAPE_FIELD)) {
								callOut.newNode(key, 1, v, null);
							}
						}
						
						
						
					}
					
					if (lhs != null) {
						// If a string is returned, optimise
						if (lhs.getType().equals(PointsToGraph.STRING_CONST.getType())) {
							callOut.assignConstant(lhs, PointsToGraph.STRING_CONST);
						} else if (lhs.getType().equals(PointsToGraph.CLASS_CONST.getType())) {
							callOut.assignConstant(lhs, PointsToGraph.CLASS_CONST);
						} else {
							if(CallGraphTransformer.safeMethod.contains(lib.toString())) {
								callOut.assignNew(lhs, splObject);
							}else {
								callOut.assignEscape(lhs);
							}
						}
					}
					
					

//					} //end isTransparent
				}
				
				resultFlow = meet(resultFlow, callOut);

			}else {
//				System.out.println("exit null for " + calledMethod);
			}
		}

		// If at least one call succeeded, result flow is not TOP
		if (resultFlow.equals(topValue())) {
			return null;
		} else {
			return resultFlow;
		}
	}


	/**
	 * Returns the union of two points-to graphs.
	 */
	@Override
	public PointsToGraph meet(PointsToGraph op1, PointsToGraph op2) {
		PointsToGraph result = new PointsToGraph();
		result.union(op1, op2);
		return result;
	}

	/**
	 * The default data flow value (lattice top) is the empty points-to graph.
	 */
	@Override
	public PointsToGraph topValue() {
		return new PointsToGraph();
	}

	@Override
	public ProgramRepresentation<SootMethod, Unit> programRepresentation() {
		return DefaultJimpleRepresentation.v();
	}

	// create global dummy object set, add all objects created by me to dummy set
	// and then at all getfield if rec is dummy then getfield should return dummy
	// for reftype
	


}