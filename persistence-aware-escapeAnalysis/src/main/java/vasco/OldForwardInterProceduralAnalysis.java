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
package vasco;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import soot.Local;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AnyNewExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.Stmt;
import soot.tagkit.BytecodeOffsetTag;
import vasco.callgraph.PointsToAnalysis;
import vasco.callgraph.PointsToGraph;
import vasco.soot.AbstractNullObj;

/**
 * A generic forward-flow inter-procedural analysis which is fully
 * context-sensitive.
 * 
 * <p>
 * This class essentially captures a forward data flow problem which can be
 * solved using the context-sensitive inter-procedural analysis framework as
 * described in {@link InterProceduralAnalysis}.
 * </p>
 * 
 * <p>
 * This is the class that client analyses will extend in order to perform
 * forward-flow inter-procedural analysis.
 * </p>
 * 
 * @author Rohan Padhye
 * 
 * @param <M> the type of a method
 * @param <N> the type of a node in the CFG
 * @param <A> the type of a data flow value
 * 
 * @deprecated This is the old API from the initial SOAP '13 submission without
 *             call/return flow functions. It is only here for a temporary
 *             period while the {@link vasco.callgraph.PointsToAnalysis
 *             PointsToAnalysis} class is migrated to the new API. After that
 *             work is done, this class will be permanently removed from VASCO.
 */
public abstract class OldForwardInterProceduralAnalysis<M, N, A> extends InterProceduralAnalysis<M, N, A> {

	/** Constructs a new forward-flow inter-procedural analysis. */
	public OldForwardInterProceduralAnalysis() {
		// Kick-up to the super with the FORWARD direction.
		super(false);
		analysisStack = new Stack<Context<M, N, A>>();
		this.allOutValues = new HashMap<SootMethod, Map<Unit,PointsToGraph>>();
//		calleeIndex = 1;
		methodIndex = 1;
		calleeIndexMap = new HashMap<String, Integer>();
		previousInMap = new HashMap<Integer, A>();
		
		//initialize data structures for reflection
	    this.classForNameReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    this.classNewInstanceReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    this.constructorNewInstanceReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    this.methodInvokeReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    this.fieldSetReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    this.fieldGetReceivers = new LinkedHashMap<SootMethod, Set<String>>();
	    
	    this.methodIndices = new HashMap<String, Integer>();
	    this.sootMethodIndices = new HashMap<SootMethod, Integer>();
	    this.sootMethodArgs = new HashMap<SootMethod, List<Local>>();
	    
	    this.callsiteReceiverReference = new HashMap<SootMethod, Map<Integer,Set<SootClass>>>();
	    this.sootClassIndices = new HashMap<SootClass, Integer>();
	    
	    //this.loadReflectionTrace();
	    this.partiallyAnalysedMethods = new HashSet<SootMethod>();
	    this.needsFixPointIn = new HashSet<SootMethod>();
	   
	    this.methodEntryFrequency = new HashMap<M, Integer>();
	    this.invocationCount = new HashMap<SootMethod, Integer>();
	    methodsOverInvocationThreshold = new HashSet<SootMethod>();
	    
	}

	public static HashMap<String, Integer> methodCallCount = new HashMap<>();
	public static Set<SootMethod> methodsOverInvocationThreshold;
	public static boolean dumpAllOuts = false;
	public static boolean applyInvocationThreshold;
	public static int methodInvocationThreshold;
	public Map<SootMethod, Integer> invocationCount;
	public Map<M, Integer> methodEntryFrequency;
	protected Stack<Context<M, N, A>> analysisStack;

	public Map<SootMethod, Map <Unit, PointsToGraph>> allOutValues;
	public Map<Integer, A> previousInMap;
	
	// consider this a unique identifier for each callee method. needed when
	// building the callsite invariants
//	public Integer calleeIndex;
	public Integer methodIndex;
	// map of method name to its calleeIndex
	public Map<String, Integer> calleeIndexMap;
	public boolean immediatePrevContextAnalysed;
	public boolean isCurrentInvocationSummarized;
	public boolean isInvoke = false;

	// structures to handle reflection
	protected final Map<SootMethod, Set<String>> classForNameReceivers;
	protected final Map<SootMethod, Set<String>> classNewInstanceReceivers;
	protected final Map<SootMethod, Set<String>> constructorNewInstanceReceivers;
	protected final Map<SootMethod, Set<String>> methodInvokeReceivers;
	protected final Map<SootMethod, Set<String>> fieldSetReceivers;
	protected final Map<SootMethod, Set<String>> fieldGetReceivers;
	
	public Map<String, Integer> methodIndices;
	
	public Map<SootMethod, Integer> sootMethodIndices;
	public Map<SootMethod, List<Local>> sootMethodArgs;
	public Map<SootMethod, Map <Integer, Set<SootClass>>> callsiteReceiverReference;
	public Map<SootClass, Integer> sootClassIndices;
	
	public Set<SootMethod> partiallyAnalysedMethods;
	
	public Set<SootMethod> needsFixPointIn;
	
	protected static Stack <SootMethod> methStack = new Stack<SootMethod>();

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void doAnalysis() {

		// System.out.println(Scene.v().getCallGraph());
		
		
		//TODO: shashin - here, fetch the list of partially analysed methods and mark them for summarising
		//	this is obviously more efficient than string comparisons later on
		try {
			
			/******* list of partially analysed methods after second pass (eclipse) *************/
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<org.eclipse.jdt.core.JavaCore: org.eclipse.jdt.core.IClasspathEntry newContainerEntry(org.eclipse.core.runtime.IPath,org.eclipse.jdt.core.IAccessRule[],org.eclipse.jdt.core.IClasspathAttribute[],boolean)>"));
			/******* list of partially analysed methods after second pass (eclipse) *************/

			/******* list of partially analysed methods after second pass (avrora) *************/
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.types.SensorSimulation$SensorNode: void setNodePosition()>"));
			/******* list of partially analysed methods after second pass (avrora) *************/
			
			
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer16Bit$OCRnxPairedRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPCRReg: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer8Bit$BufferedRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.clock.DerivedClock: void removeEvent(avrora.sim.Simulator$Event)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.types.SensorSimulation$SensorNode: void setNodePosition()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPDReg$TransmitRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer8Bit$BufferedRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer16Bit$BufferedRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer16Bit$PairedRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer8Bit$ControlRegister: void forcedOutputCompare()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$BitRangeView: void setValue(int)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister$TwoLevelFIFO: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void unpostADCInterrupt()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$PermutedView: int getValue()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$UBRRnLReg: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void stopConversion()>"));

//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: void setSPIF()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI: void postSPIInterrupt()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister$TwoLevelFIFO: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.types.SensorSimulation$SensorNode: void createNode()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI: void access$000(avrora.sim.mcu.SPI)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void stopConversion()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$BitRangeView: void setValue(int)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void unpostADCInterrupt()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: void clearSPIF()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.types.SensorSimulation$SensorNode: void instantiate()>"));

			/******* list of partially analysed methods after second pass (avrora) *************/

//			this.partiallyAnalysedMethods.add(Scene.v().getMethod(""));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer8Bit$BufferedRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$UBRRnHReg: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: void clearSPIF()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI: void access$000(avrora.sim.mcu.SPI)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI$SPSReg: void setSPIF()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.types.SensorSimulation$SensorNode: void setNodePosition()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.clock.DerivedClock: long getCount()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$PermutedView: void setValue(int)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$BitRangeView: int getValue()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$BitRangeView: void setValue(int)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.state.RegisterUtil$PermutedView: int getValue()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void stopConversion()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister: void write(byte)>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.ADC$ControlRegister: void unpostADCInterrupt()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.USART$DataRegister$TwoLevelFIFO: byte read()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.SPI: void postSPIInterrupt()>"));
//			this.partiallyAnalysedMethods.add(Scene.v().getMethod("<avrora.sim.mcu.Timer16Bit$BufferedRegister: void write(byte)>"));
			
//			System.out.println(Scene.v().getSootClass("org.sunflow.core.accel.KDTree").getMethodByNameUnsafe("build").getActiveBody());
		} catch (RuntimeException rex) {
			assert(false) : rex.toString();
		}

		// Initialise the MAIN context
		for (M entryPoint : programRepresentation().getEntryPoints()) {
			Context<M, N, A> context = new Context<M, N, A>(entryPoint,
					programRepresentation().getControlFlowGraph(entryPoint), false);
			A boundaryInformation = boundaryValue(entryPoint);
			initContext(context, boundaryInformation);

		}

		// Stack-of-work-lists data flow analysis.
		while (!analysisStack.isEmpty()) {
			// Get the context at the top of the stack.
			Context<M, N, A> context = analysisStack.peek();

			// Either analyse the next pending unit or pop out of the method
			if (!context.getWorkList().isEmpty()) {

				// work-list contains items; So the next unit to analyse.
				N unit = context.getWorkList().pollFirst();
				
				if (unit != null) {
					int unitBCI = -1;
						BytecodeOffsetTag bT = (BytecodeOffsetTag) ((Unit) unit).getTag("BytecodeOffsetTag");
						if(bT != null)
							unitBCI = bT.getBytecodeOffset();

					// Compute the IN data flow value (only for non-entry units).
					List<N> predecessors = context.getControlFlowGraph().getPredsOf(unit);
					if (predecessors.size() != 0) {
						// Merge all the OUT values of the predecessors
						Iterator<N> predIterator = predecessors.iterator();
						// Initialise IN to the OUT value of the first predecessor
						A in = context.getValueAfter(predIterator.next());
						// Then, merge OUT of remaining predecessors with the
						// intermediate IN value
						while (predIterator.hasNext()) {
							A predOut = context.getValueAfter(predIterator.next());
							in = meet(in, predOut);
						}
						// Set the IN value at the context
						context.setValueBefore(unit, in);
						
					} else {
						//now processing an entry unit
						if (!context.getMethod().toString().contains("clinit")) {
							methStack.push((SootMethod) context.getMethod());
						}
					}
					
					if(context.getControlFlowGraph().getHeads().contains(unit)) {
						SootMethod method = (SootMethod)context.getMethod();
						int invocationCount = this.invocationCount.getOrDefault(method, 0);
						methodCallCount.put(method.toString(), invocationCount);
						
//						System.out.println("=====================================================");
						
						if(!methodsOverInvocationThreshold.contains(method)) {
							if(applyInvocationThreshold && 
									invocationCount > methodInvocationThreshold ) {
								System.err.println(context.getMethod() + " over invocation threshold");
								//add this method to the ignore list
								methodsOverInvocationThreshold.add((SootMethod)context.getMethod());
								//reinitialize the callers and add  them back to the analysis stack
								Set<CallSite <M, N, A>> callersSet = contextTransitions.getContextInsensitiveCallersForMethod(context.getMethod());
								addCallersForAnalysis(callersSet);
								context.getWorkList().clear();
								continue;
							} else {
								this.invocationCount.put( method, ++invocationCount);
							}
						}
		
						
					}
					// Store the value of OUT before the flow function is processed.
					A prevOut = context.getValueAfter(unit);
				
			

					// Get the value of IN
					A in = context.getValueBefore(unit);



					// Now perform the flow function.
					this.immediatePrevContextAnalysed = false;
					this.isCurrentInvocationSummarized = false;
					
//					System.out.println("context: " + context.toString() + " -- method: "  + ((SootMethod) context.getMethod()) + " -- unit: " + unit.toString());
					A out = flowFunction(context, unit, in);
					

					if (out == null) {
						out = prevOut;
					}

					// Set the OUT value
					context.setValueAfter(unit, out);

					if ( /*(!isLoopHeader   && immediatePrevContextAnalysed  ) || */ out.equals(prevOut) == false) {
						//System.out.println("OUT changed @" + unitBCI);

						// Then add successors to the work-list.
						for (N successor : context.getControlFlowGraph().getSuccsOf(unit)) {
							//System.out.println("ADDING TO WORKLIST FROM doAnalysis, line 228");
							context.getWorkList().add(successor);
						}
						// If the unit is in TAILS, then we have at least one
						// path to the end of the method, so add the NULL unit
						if (context.getControlFlowGraph().getTails().contains(unit)) {
							//System.out.println("ADDING null TO WORKLIST FROM doAnalysis, line 234");
							context.getWorkList().add(null);
						}
					} else {
//						if(context.getMethod().toString().equals("<org.sunflow.core.Scene: void render(org.sunflow.core.Options,org.sunflow.core.ImageSampler,org.sunflow.core.Display)>")) {
//							System.out.println("******** out = prevout ***********");
//						}
					}

				} else {
					// NULL unit, which means the end of the method.
					assert (context.getWorkList().isEmpty());
					
//					System.out.println("completed: " + getTrimmedByteCodeSignature((SootMethod) context.getMethod()));

					// Exit flow value is the merge of the OUTs of the tail nodes.
					A exitFlow = topValue();
					for (N tail : context.getControlFlowGraph().getTails()) {
						A tailOut = context.getValueAfter(tail);
						exitFlow = meet(exitFlow, tailOut);
					}
					// Set the exit flow of the context.
					boolean shouldAnalyzeCallers = !exitFlow.equals(context.getExitValue());
//					shouldAnalyzeCallers = true;
					context.setExitValue(exitFlow);
					

					// Mark this context as analysed at least once.
					context.markAnalysed();
					
					 /**************************************************************************************/
					 //add callers context-insensitive
				
					 if(shouldAnalyzeCallers) {


			
							//1. obtain the callers of this context
							Set<CallSite <M, N, A>> callersSet = contextTransitions.getContextInsensitiveCallersForMethod(context.getMethod());
							//only proceed if we have callers!
							if(callersSet != null) {
								//2. obtain the unique set of caller methods from these contexts;
								Set <SootMethod> callerMethods = new HashSet <SootMethod>();
								for(CallSite <M, N, A> cs : callersSet) {
									callerMethods.add((SootMethod) cs.getCallingContext().getMethod());
								}
								
								//3. now we have a list of unique caller methods for this callee context
								//3a		fetch each of their contexts
								for(SootMethod callerMethod : callerMethods) {
									
									Context<M,N,A> callingContext = contexts.get(callerMethod);
									//3b. reset the worklist to the entry of the CFG (to ensure reanalysis of the method
									callingContext.getWorkList().clear();
									// First initialise all points to default flow value.
									for (N n : callingContext.getControlFlowGraph()) {
										callingContext.setValueBefore(n, topValue());
										callingContext.setValueAfter(n, topValue());
									}
									for (N head : callingContext.getControlFlowGraph().getHeads()) {
										callingContext.setValueBefore(head, copy(callingContext.getEntryValue()));
										// Add entry points to work-list
										//System.out.println("ADDING TO WORKLIST FROM initContext, line 392");
										callingContext.getWorkList().add(head);
									}
									
									//3c. clear the out values
		//							callingContext.clearOutValues();
									//3d. leave the exit value alone!
									
									//3e. remove this context from the analysis stack, if it exists, and reinsert this new context
	//								analysisStack.remove(callingContext);
									if(!analysisStack.contains(callingContext))
										analysisStack.add(callingContext);
									
									
								}
							}	
						}
//					 } //end if shouldAnalyzeCallers
					 
					 /**************************************************************************************/
					 

					// Free memory on-the-fly if not needed
					if (freeResultsOnTheFly) {
						Set<Context<M, N, A>> reachableContexts = contextTransitions.reachableSet(context, true);
						// If any reachable contexts exist on the stack, then we cannot free memory
						boolean canFree = true;
						for (Context<M, N, A> reachableContext : reachableContexts) {
							if (analysisStack.contains(reachableContext)) {
								canFree = false;
								break;
							}
						}
						// If no reachable contexts on the stack, then free memory associated
						// with this context
						if (canFree) {
							for (Context<M, N, A> reachableContext : reachableContexts) {
								reachableContext.freeMemory();
							}
						}
					}
				}
				this.isCurrentInvocationSummarized = false;
			} else {
				// If work-list is empty, then remove it from the analysis.
				analysisStack.remove(context);
			}
		}

		// Sanity check
		for (Context<M, N, A> context : contexts.values()) {
			if (context.isAnalysed() == false) {
				System.err.println(
						"*** ATTENTION ***: Only partial analysis of X" + context + " " + context.getMethod());
				
			}
		}
		
		
		processMonomorphicCalls();
		if(PointsToAnalysis.dumpAllOuts) {
			processAllPointsToInformation();
		}
		
	}
	
	private void processMonomorphicCalls() { 
		
		int instanceInvokeCount = 0;
		int monomorphCount = 0;

		PointsToAnalysis pta = (PointsToAnalysis) this;
		for(Context <SootMethod, Unit, PointsToGraph> context : pta.contexts.values()) {
			if(context.isAnalysed()) {
				SootMethod m = context.getMethod();
					for(Unit unit : m.getActiveBody().getUnits()) {
						assert (unit instanceof Stmt);
						Stmt stmt = (Stmt) unit;

						//we need to handle both LHS = InvokeExpr; and InvokeStmt;
						InvokeExpr expr = null;
						if(stmt instanceof DefinitionStmt) {
							Value rhsOp = ((DefinitionStmt) stmt).getRightOp();
							if(rhsOp instanceof InvokeExpr) {
								//1. LHS = InvokeExpr;
								expr = (InvokeExpr) rhsOp;
							}
						} else if (stmt instanceof InvokeStmt) {
							//2. InvokeStmt;
							expr = stmt.getInvokeExpr();
						}
						
						if(expr != null) {
							//do we really need to avoid counting constructors and clinit's?
							//..for all programs? Can constructors be inlined in Java?
							if(expr instanceof InstanceInvokeExpr && 
									!expr.getMethod().getName().contains("<init>") && 
									!expr.getMethod().getName().contains("<clinit>")) {
								instanceInvokeCount ++;
							//if(expr instanceof InterfaceInvokeExpr || expr instanceof VirtualInvokeExpr) {
								Local receiver = (Local) ((InstanceInvokeExpr) expr).getBase();
								//get the IN value for this instruction
								PointsToGraph in = context.getValueBefore(unit);
								//get the points-to set of the receiver
								Set<AnyNewExpr> pointees = in.getTargets(receiver);
								SootClass sc = null;
								boolean isMonomorph = true;
								if(pointees.isEmpty()) {
									isMonomorph = false;
								} else {
									for(AnyNewExpr n : pointees) {
										//is this really needed??
										//assert(receiver.getType() instanceof RefType);
										if( !(n instanceof AbstractNullObj) && !PointsToAnalysis.summaryObject.contains(n) && n != PointsToGraph.PERSISTENT_NODE && n!= PointsToGraph.ESCAPE_NODE && !(n instanceof NewArrayExpr)) {
											if(sc == null)
												sc = ((RefType) n.getType()).getSootClass();
											else if(sc != ((RefType) n.getType()).getSootClass()) {
												isMonomorph = false;
												break;
											}
										} else {
											isMonomorph = false;
											break;
										}
									}
								}
								
								if(isMonomorph) {
									//System.out.println("monomorph " + unit);
									monomorphCount ++;
								}
							}
						}
					}
				}
		}
		
//		System.out.println("InstanceInvokes = " + instanceInvokeCount + "; Monomorphs = " + monomorphCount);
	}
	
	private void addCallersForAnalysis(Set<CallSite<M, N, A>> callers) {
			//only proceed if we have callers!
			if(callers != null) {
				//2. obtain the unique set of caller methods from these contexts;
				Set <SootMethod> callerMethods = new HashSet <SootMethod>();
				for(CallSite <M, N, A> cs : callers) {
					callerMethods.add((SootMethod) cs.getCallingContext().getMethod());
				}
				
				//3. now we have a list of unique caller methods for this callee context
				//3a		fetch each of their contexts
				for(SootMethod callerMethod : callerMethods) {
					Context<M,N,A> callingContext = contexts.get(callerMethod);
					//3b. reset the worklist to the entry of the CFG (to ensure reanalysis of the method
					callingContext.getWorkList().clear();
					// First initialise all points to default flow value.
					for (N n : callingContext.getControlFlowGraph()) {
						callingContext.setValueBefore(n, topValue());
						callingContext.setValueAfter(n, topValue());
					}
					for (N head : callingContext.getControlFlowGraph().getHeads()) {
						callingContext.setValueBefore(head, copy(callingContext.getEntryValue()));
						// Add entry points to work-list
						//System.out.println("ADDING TO WORKLIST FROM initContext, line 392");
						callingContext.getWorkList().add(head);
					}
					
					//3c. clear the out values
//							callingContext.clearOutValues();
					//3d. leave the exit value alone!
					
					//3e. remove this context from the analysis stack, if it exists, and reinsert this new context
//								analysisStack.remove(callingContext);
					if(!analysisStack.contains(callingContext))
						analysisStack.add(callingContext);
					
					
				}
			}	
	}

	
	
	private void processAllPointsToInformation() {
		
		PointsToAnalysis pta = (PointsToAnalysis) this;
		for(Context <SootMethod, Unit, PointsToGraph> context : pta.contexts.values()) {
			if(context.isAnalysed()) {
				SootMethod method = (SootMethod) context.getMethod();
				Map<Unit, PointsToGraph> outValues = context.getOutValues();
				this.allOutValues.put(method, outValues);
			}
			
		}
	}


	
	
	public String getTrimmedByteCodeSignature(SootMethod m) {
		String methodSig = m.getBytecodeSignature();
		String sig = methodSig.replace(".", "/").replace(": ", ".").substring(1, methodSig.length() - 2);
		return sig;
	}
	/**
	 * Creates a new context and initialises data flow values.
	 * 
	 * <p>
	 * The following steps are performed:
	 * <ol>
	 * <li>Initialise all nodes to default flow value (lattice top).</li>
	 * <li>Initialise the entry nodes (heads) with a copy of the entry value.</li>
	 * <li>Add entry points to work-list.</li>
	 * <li>Push this context on the top of the analysis stack.</li>
	 * </ol>
	 * </p>
	 * 
	 * @param context    the context to initialise
	 * @param entryValue the data flow value at the entry of this method
	 */
	protected void initContext(Context<M, N, A> context, A entryValue) {
		// Get the method
		M method = context.getMethod();

		// First initialise all points to default flow value.
		for (N unit : context.getControlFlowGraph()) {
			context.setValueBefore(unit, topValue());
			context.setValueAfter(unit, topValue());
		}

		// Now, initialise entry points with a copy of the given entry flow.
		context.setEntryValue(copy(entryValue));
		for (N unit : context.getControlFlowGraph().getHeads()) {
			context.setValueBefore(unit, copy(entryValue));
			// Add entry points to work-list
			//System.out.println("ADDING TO WORKLIST FROM initContext, line 392");
			context.getWorkList().add(unit);
		}

		// Add this new context to the given method's mapping.
		if (!contexts.containsKey(method)) {
			contexts.put(method, context);
		}

		// Push this context on the top of the analysis stack.
		analysisStack.add(context);

		// SHASHIN

		SootMethod sMethod = (SootMethod) context.getMethod();
		String sig = getTrimmedByteCodeSignature(sMethod);
		int index = this.methodIndices.size();
		//maintain an index for each unique method signature
		if(! this.methodIndices.containsKey(sig)) {
			this.methodIndices.put(sig, ++index);
			
			//System.out.println("start: " + sMethod.toString() + " method indices count " + methodIndices.size()); 
		} else {
//			System.out.println(sig + " already exists in indices map"); 
			
		}

		int index2 = this.sootMethodIndices.size();
		//maintain an index for each unique method signature
		if(! this.sootMethodIndices.containsKey(sMethod)) {
			this.sootMethodIndices.put(sMethod, ++index2);
		}
		
		if(! this.sootMethodArgs.containsKey(sMethod)) {
			List<Local> refParamLocals = new ArrayList<Local>();
			if(! sMethod.isStatic()) {
				//method is non-static, valid this-param exists
				Local thisLocal = sMethod.getActiveBody().getThisLocal();
				refParamLocals.add(thisLocal);
			}
			
			for(int i = 0; i < sMethod.getParameterCount(); i++) {
				if(sMethod.getParameterType(i) instanceof RefLikeType) {
					Local parameterLocal = sMethod.getActiveBody().getParameterLocal(i);
					refParamLocals.add(parameterLocal);
				}
			}
			
			this.sootMethodArgs.put(sMethod, refParamLocals);
		}
	}

	/**
	 * Processes a call statement.
	 * 
	 * <p>
	 * Retrieves a value context for the callee if one exists with the given entry
	 * value, or else creates a new one and adds the transition to the context
	 * transition table.
	 * </p>
	 * 
	 * <p>
	 * If the callee context has already been analysed, returns the resulting exit
	 * value. For newly created contexts the result would be <tt>null</tt>, as they
	 * are obviously not analysed even once.
	 * </p>
	 * 
	 * <p>
	 * Note that this method is not directly called by {@link #doAnalysis()
	 * doAnalysis}, but is instead called by
	 * {@link #flowFunction(Context, Object, Object) flowFunction} when a method
	 * call statement is encountered. The reason for this design decision is that
	 * client analyses may want their own setup and tear down sequences before a
	 * call is made (similar to edge flow functions at the call and return site).
	 * Also, analyses may want to choose which method call to process at an invoke
	 * statement in the case of virtual calls (e.g. a points-to analysis may build
	 * the call-graph on-the-fly).
	 * </p>
	 * 
	 * <p>
	 * Therefore, it is the responsibility of the client analysis to detect an
	 * invoke expression when implementing
	 * {@link #flowFunction(Context, Object, Object) flowFunction}, and suitably
	 * invoke {@link #processCall(Context, Object, Object, Object) processCall} with
	 * the input data flow value which may be different from the IN/OUT value of the
	 * node due to handling of arguments, etc. Similarly, the result of
	 * {@link #processCall(Context, Object, Object, Object) processCall} may be
	 * modified by the client to handle return values, etc. before returning from
	 * {@link #flowFunction(Context, Object, Object) flowFunction}. Ideally,
	 * {@link #flowFunction(Context, Object, Object) flowFunction} should return
	 * <tt>null</tt> if and only if
	 * {@link #processCall(Context, Object, Object, Object) processCall} returns
	 * <tt>null</tt>.
	 * 
	 * @param callerContext the analysis context at the call-site
	 * @param callNode      the calling statement
	 * @param method        the method being called
	 * @param entryValue    the data flow value at the entry of the called method.
	 * @return the data flow value at the exit of the called method, if available,
	 *         or <tt>null</tt> if unavailable.
	 */
	protected A processCall(Context<M, N, A> callerContext, N callNode, M method, A entryValue) {
		/*
		 * TODO: to keep things in sync with our JITC components, we want to analyze methods context insensitively.
		 * 		
		 * basically, check if the current entry value is subsumed by the entry value in the context already analyzed,
		 * if so - then no change.
		 * but if not -instead of creating a new context below, perform a meet of the entry value with the entry value in the (singleton) context of the method
		 * 
		 */

		CallSite<M, N, A> callSite = new CallSite<M, N, A>(callerContext, callNode);

		// Check if the called method has a context associated with this entry flow:
		Context<M, N, A> calleeContext = getContext(method, entryValue);
		// If not, then set 'calleeContext' to a new context with the given entry flow.
		if (calleeContext == null) {
			//previously - this context is not analyzed/first time analyzed
			//calleeContext = mergeContexts(thisContext, getContexts(method))
			//assert (calleeContext.isAnalysed || hasChanged == false);
			
			calleeContext = new Context<M, N, A>(method, programRepresentation().getControlFlowGraph(method), false);
			initContext(calleeContext, entryValue);
			if (verbose) {
				System.out.println("[NEW] X" + callerContext + " -> X" + calleeContext + " " + method + " ");
			}
		}

		// Store the transition from the calling context and site to the called context.
		contextTransitions.addTransition(callSite, calleeContext);

		// Check if 'caleeContext' has been analysed (surely not if it is just newly
		// made):
		if (calleeContext.isAnalysed()) {
			if (verbose) {
				System.out.println("[HIT] X" + callerContext + " -> X" + calleeContext + " " + method + " ");
			}
			// If yes, then return the 'exitFlow' of the 'calleeContext'.
			return calleeContext.getExitValue();
		} else {
			// If not, then return 'null'.
			return null;
		}
	}

	/*
	 * Context-Insensitive variant of processCall() above
	 * 
	 */
	protected A processCallContextInsensitive2(Context<M, N, A> callerContext, N callNode, M method, A entryValue) {
		
		return null;
	}
	/*
	 * Context-Insensitive variant of processCall() above
	 * 
	 */
	protected A processCallContextInsensitive(Context<M, N, A> callerContext, N callNode, M method, A entryValue) {
		
//		System.out.println("processCallContextInsensitive : " + method.toString());
//		if(method.toString().equals("<org.dacapo.harness.Benchmark: void prepareJars()>")) {
////					if(method.toString().equals("<org.dacapo.harness.Benchmark: java.lang.String fileInScratch(java.lang.String)>")) {
//						System.out.println("process call entry");
//						System.out.println("caller: " + callerContext.getMethod());
//						System.out.println(entryValue);
//					}
		
		Context <M, N, A> calleeContext;
		
		
		
		
		/*
		 * if some method is getting invoked over a threshold value, treat is as a library method
		 * 
		 * in order to accomplish that:
		 *  1. maintain a invocation count map
		 *  2. if invocation count > threshold
		 *  	2a. add method to list of methods to summarize
		 *  	2b. if method is already analyzed, set its return to BOT, to make sure its callers are re-analyzed (out will have changed)
		 */
		
//		if(applyInvocationThreshold) {
//			int invocationCount = this.invocationCount.getOrDefault((SootMethod) method, 0);
//			if(invocationCount > methodInvocationThreshold) {
//				//take action
//				System.err.println(method + " over invocation threshold");
//				//save this method to the ignore list
//				methodsOverInvocationThreshold.add((SootMethod) method);
//				//reinitialize the callers and add  them back to the analysis stack
//				Set<CallSite <M, N, A>> callersSet = contextTransitions.getContextInsensitiveCallersForMethod(method);
//				addCallersForAnalysis(callersSet);
//				//return nothing, context is not analysed (discarded, rather)
//				return null;
//				
//				
//			} else {
//				this.invocationCount.put((SootMethod) method, ++invocationCount);
//			}
//		}
			

		if(contexts.containsKey(method)) {
			//a context exists for this method
			calleeContext = getContext(method, null);
			
			
			
			//1. check to see if entry value has changed
			A aggregateEntryValue = meet(entryValue, calleeContext.getEntryValue());
			
			boolean hasEntryChanged = ! calleeContext.getEntryValue().equals(aggregateEntryValue);
			
			//2. if entry value has changed, perform cleanup:
			if(hasEntryChanged) {
				this.needsFixPointIn.add((SootMethod) method);
				
//				if(calleeContext.getMethod().toString().contains("<org.h2.value.Value: org.h2.value.Value convertTo(int)>")) {
//					System.out.println("Entry value is");
//					System.out.println((PointsToGraph)calleeContext.getEntryValue());
//					System.out.println("***********************************************");
//					System.out.println("new in after merge is ");
//					System.out.println((PointsToGraph)entryValue);
//				}
				
				
//				int invocationCount = this.invocationCount.getOrDefault((SootMethod) method, 0);
//				if(applyInvocationThreshold && invocationCount > methodInvocationThreshold ) {
//					//take action
//					System.err.println((SootMethod) method + " over invocation threshold");
//					//save this method to the ignore list
//					methodsOverInvocationThreshold.add((SootMethod) method);
//					//reinitialize the callers and add  them back to the analysis stack
//					Set<CallSite <M, N, A>> callersSet = contextTransitions.getContextInsensitiveCallersForMethod(method);
//					addCallersForAnalysis(callersSet);
//					//return nothing, context is not analysed (discarded, rather)
//				} else {
////				}
//				
//					this.invocationCount.put((SootMethod) method, ++invocationCount);
	//				System.out.println("change to context insensitive in-summary");
					//2a. set context entry value to the new entry value
					calleeContext.setEntryValue(aggregateEntryValue);
					//2b. reset before/after values of all units
					for(N unit : calleeContext.getControlFlowGraph()) {
						calleeContext.setValueAfter(unit, topValue());
						calleeContext.setValueBefore(unit, topValue());
					}
					
					//2c. reset worklist to head of CFG
					calleeContext.getWorkList().clear();
					for(N head : calleeContext.getControlFlowGraph().getHeads()) {
						calleeContext.setValueBefore(head, copy(calleeContext.getEntryValue()));
						calleeContext.getWorkList().add(head);
					}
					
	//				calleeContext.unmarkAnalysed();
					
					//2d. we (do not) need to replace this context on the analysis stack, if it exists
					analysisStack.remove(calleeContext);
					analysisStack.push(calleeContext);
//				}
				
			}
			
		} else {
			//new context has to be created
			calleeContext = new Context <M, N, A> (method, programRepresentation().getControlFlowGraph(method), false);

			initContext(calleeContext, entryValue);
			
		}
		
		CallSite <M, N, A> callSite = new CallSite<M, N, A>(callerContext, callNode);
		contextTransitions.addContextInsensitiveCaller(callSite, method);
		
		
		//TODO: make this context insensitive. instead of calleecontext, make the map the method name
		// essentially, when we do get callers, we want ALL callsites later - not just the callsites that called with this specific context
//		contextTransitions.addTransition(callSite, calleeContext);
		//simpler way - maintain a map of callsites, to the called methods
		//then later, when a method is marked analyzed - simply fetch all its callers irrespective of context and add them to the worklist (BOOM !)
		
		// Check if 'caleeContext' has been analysed (surely not if it is just newly
		// made):
		if (calleeContext.isAnalysed()) {
			if (verbose) {
				System.out.println("[HIT] X" + callerContext + " -> X" + calleeContext + " " + method + " ");
			}
			// If yes, then return the 'exitFlow' of the 'calleeContext'.
//		if(method.toString().equals("<org.dacapo.harness.Benchmark: void prepareJars()>")) {
////					if(method.toString().equals("<org.dacapo.harness.Benchmark: java.lang.String fileInScratch(java.lang.String)>")) {
//						System.out.println("process call exit");
//						System.out.println(calleeContext.getExitValue());
			
//					}
		
			
			return calleeContext.getExitValue();
		} else {
			// If not, then return 'null'.
//			System.out.println("context " + calleeContext + " not analysed, null out");
//		if(method.toString().equals("<org.dacapo.harness.Benchmark: void prepareJars()>")) {
////					if(method.toString().equals("<org.dacapo.harness.Benchmark: java.lang.String fileInScratch(java.lang.String)>")) {
//						System.out.println("process call exit");
//						System.out.println("null");
//					}
			return null;
		}
		
	}

	protected abstract A flowFunction(Context<M, N, A> context, N unit, A in);

}
