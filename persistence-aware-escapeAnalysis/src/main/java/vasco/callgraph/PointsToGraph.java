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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.ArrayType;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.Type;
import soot.jimple.AnyNewExpr;
import soot.jimple.ClassConstant;
import soot.jimple.Constant;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JimpleLocal;
import soot.util.Chain;
import vasco.soot.AbstractNullObj;

/**
 * A data flow value representation for points-to analysis using allocation
 * sites.
 * 
 * <p>
 * The points-to graph contains two types of edges: (1) from root variables
 * ({@link soot.Local Local}) to objects represented by allocation sites
 * ({@link soot.jimple.AnyNewExpr AnyNewExpr}), and (2) from objects to objects
 * along fields ({@link soot.SootField SootField}).
 * </p>
 * 
 * <p>
 * Special artificial locals are used for string constants, class constants,
 * return values, etc. and artificial sites are used for summary nodes. For
 * arrays an artificial field is used to represent element access.
 * </p>
 * 
 * @author Rohan Padhye
 */
public class PointsToGraph {

	static boolean rc = false;
	
	public static final SootField ARRAY_FIELD = new SootField("[]", Scene.v().getObjectType());
	public static final SootField ESCAPE_FIELD = new SootField("MAY_ESCAPE", Scene.v().getObjectType());
	public static final SootField PERSISTENT_FIELD = new SootField("MAY_PERSIST", Scene.v().getObjectType());
	public static final SootField SUMMARY_FIELD = new SootField("SUMMARY", Scene.v().getObjectType());
	public static final SootField OBJECT_FIELD = new SootField("F[]", Scene.v().getObjectType());
	public static final Local GLOBAL_LOCAL = new JimpleLocal("@global", Scene.v().getObjectType());
	public static final Local RETURN_LOCAL = new JimpleLocal("@return", Scene.v().getObjectType());
	public static final Local STICKY_LOCAL = new JimpleLocal("@params", Scene.v().getObjectType());
	public static final Constant STRING_CONST = StringConstant.v("GLOBAL STRING CONSTANT");
	public static final Constant CLASS_CONST = ClassConstant.v("java/lang/Object");

	public static final NewExpr STRING_SITE = new JNewExpr(Scene.v().getRefType("java.lang.String"));
	public static final NewExpr CLASS_SITE = new JNewExpr(Scene.v().getRefType("java.lang.Class"));
	
	public static final NewExpr SUMMARY_NODE = new JNewExpr(null);
	//public static final NewExpr CAUGHT_NODE = new JNewExpr(null);
	public static final NewExpr ESCAPE_NODE = new JNewExpr(null);
	public static final NewExpr PERSISTENT_NODE = new JNewExpr(null);
	public static final NewExpr GLOBAL_SITE = new JNewExpr(Scene.v().getObjectType());

	public static final AbstractNullObj nullObj = new AbstractNullObj();

	protected Map<Local, Set<AnyNewExpr>> roots;
	protected Map<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>> heap;

	public static Map<SootField, Integer> fieldIntMap = new HashMap<SootField, Integer>();

	/**
	 * Constructs a new empty points-to graph.
	 */
	public PointsToGraph() {
		roots = new HashMap<Local, Set<AnyNewExpr>>();
		heap = new HashMap<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>>();
		// SHASHIN
		heap.put(nullObj, new HashMap<SootField, Set<AnyNewExpr>>());
	}

	/**
	 * Constructs a copy of the given points-to graph.
	 * 
	 * @param other the points-to graph to copy
	 */
	public PointsToGraph(PointsToGraph other) {
		// As the data inside the top-level maps are immutable, just a shallow
		// copy will suffice
		this.roots = new HashMap<Local, Set<AnyNewExpr>>(other.roots);
		this.heap = new HashMap<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>>(other.heap);
		
		heap.put(nullObj, new HashMap<SootField, Set<AnyNewExpr>>());
	}

	/**
	 * Adds an edge between two sites with a given field.
	 */
	@SuppressWarnings("unused")
	private void addEdge(AnyNewExpr n1, SootField field, AnyNewExpr n2) {
		// No edge from null
		assert_tmp(n1 != null && n2 != null && field != null);

		// Ensure nodes exist in the heap
		ensureNode(n1);
		ensureNode(n2);

		// Add the field edge to a copy of the current edges.
		Map<SootField, Set<AnyNewExpr>> oldEdges = heap.get(n1);
		Map<SootField, Set<AnyNewExpr>> newEdges = new HashMap<SootField, Set<AnyNewExpr>>(oldEdges);
		Set<AnyNewExpr> oldTargets = oldEdges.containsKey(field) ? oldEdges.get(field) : new HashSet<AnyNewExpr>();
		Set<AnyNewExpr> newTargets = new HashSet<AnyNewExpr>(oldTargets);
		boolean change = newTargets.add(n2);
		if (change) {
			newEdges.put(field, Collections.unmodifiableSet(newTargets));
			heap.put(n1, Collections.unmodifiableMap(newEdges));
		}
	}

	/**
	 * Adds an edge between a variable and a node.
	 */
	@SuppressWarnings("unused")
	private void addEdge(Local var, AnyNewExpr node) {
		assert_tmp(var != null && node != null);

		// Ensure entry exists for field edges.
		ensureNode(node);

		// Add the root variable edge.
		Set<AnyNewExpr> oldPointees = roots.containsKey(var) ? roots.get(var) : new HashSet<AnyNewExpr>();
		Set<AnyNewExpr> newPointees = new HashSet<AnyNewExpr>(oldPointees);
		boolean change = newPointees.add(node);
		if (change) {
			roots.put(var, Collections.unmodifiableSet(newPointees));
		}
	}

	/**
	 * Returns <tt>true</tt> only if there is an edge from the given root variable
	 * to the given heap node.
	 */
	public boolean containsEdge(Local var, AnyNewExpr node) {
		return roots.get(var).contains(node);
	}

	/**
	 * Assigns a root variable to a root variable.
	 */
	public void assign(Local lhs, Local rhs, boolean isCasting) {
		// Find whatever the RHS was pointing to.
		Set<AnyNewExpr> rhsTargets = roots.get(rhs);

		// We will fill this up with correctly typed targets
		Set<AnyNewExpr> lhsTargets = new HashSet<AnyNewExpr>();
		Type lhsType = lhs.getType();
		if (lhsType instanceof ArrayType) {
			lhsType = ((ArrayType) lhsType).baseType;
		}
		if (rhsTargets != null) {
			// Handle references and arrays separately
			if (lhsType instanceof RefType) {
				
				SootClass toClass = ((RefType) lhsType).getSootClass();
				for (AnyNewExpr rhsTarget : rhsTargets) {
					// Handle only instance objects
					if (rhsTarget instanceof AnyNewExpr) {
						// Do not type-check for summary nodes and when the LHS is java.lang.Object
						if (PointsToAnalysis.summaryObject.contains(rhsTarget) || rhsTarget == PERSISTENT_NODE || rhsTarget == ESCAPE_NODE || lhsType.equals(Scene.v().getObjectType())) {
							lhsTargets.add(rhsTarget);
							continue;
						}
						Type rhsTargetType = rhsTarget.getType();
						if (rhsTargetType instanceof ArrayType) {
							rhsTargetType = ((ArrayType) rhsTargetType).baseType;
						}
						
						if (rhsTargetType instanceof RefType) {
							SootClass fromClass = ((RefType) rhsTargetType).getSootClass();

							
							//shashin: removing this check for now, it causes issues when classes are missing on the classpath
							if (PointsToGraph.canCast(fromClass, toClass)) {
								// Yes, add this target
								lhsTargets.add(rhsTarget);
								
							}else if(isCasting) { //&& PointsToGraph.canCast(toClass, fromClass)) {
								lhsTargets.add(rhsTarget);
							}
						} else {
							// For non-ref base types (e.g. char[]), just add
							lhsTargets.add(rhsTarget);
						}
					}
				}
			} else if (lhsType instanceof ArrayType) {
				// We are not so fickle about arrays
				lhsTargets.addAll(rhsTargets);
			} else {
				//we will end up here if we have an int[] or (other primitive array) - assign to keep ptgs sanitized
				lhsTargets.addAll(rhsTargets);
			}
		}

		// Add the targets to the LHS edges.
		roots.put(lhs, Collections.unmodifiableSet(lhsTargets));

	}
	
		
	public Set<AnyNewExpr> getPointsTo(Local rhs){
		return roots.get(rhs);
	}
	
	/**
	 * Assigns a constant to a root variable.
	 */
	public void assignConstant(Local lhs, Constant rhs) {
		// Get the allocation site of this constant
		NewExpr newExpr = constantNewExpr(rhs);
		// If it was a null constant, assign null, otherwise assign alloc site
		if (newExpr == null) {
			Set<AnyNewExpr> lhsTargets = new HashSet<>();
			lhsTargets.add(nullObj);
			roots.put(lhs, Collections.unmodifiableSet(lhsTargets));
		} else {
			assignNew(lhs, newExpr);
		}
	}

	/**
	 * Assigns the sticky local to a parameter.
	 */
	public void assignSticky(Local sticky, Local parameter) {
		Set<AnyNewExpr> rhsTargets = roots.get(parameter);
		Set<AnyNewExpr> lhsTargets = new HashSet<AnyNewExpr>(roots.get(sticky));
//		try {
		boolean change = lhsTargets.addAll(rhsTargets);
		if (change) {
			roots.put(sticky, Collections.unmodifiableSet(lhsTargets));
		} 
//		} catch (NullPointerException nex) { 
//			System.out.println("assignSticky nex");
//		}
	}

	/**
	 * Assigns a root variable to a new object at a given allocation site.
	 */
	public void assignNew(Local lhs, AnyNewExpr allocSite) {

		// If creating a new string or class, re-use the constant site
		if (allocSite != PERSISTENT_NODE && allocSite != ESCAPE_NODE && !PointsToAnalysis.summaryObject.contains(allocSite) && allocSite != nullObj) {
			if (allocSite.getType().equals(STRING_CONST.getType())) {
				allocSite = STRING_SITE;
			} else if (allocSite.getType().equals(CLASS_CONST.getType())) {
				allocSite = CLASS_SITE;
			}
		}

		// We do not handle multi-dimensional arrays in this version
		if (allocSite instanceof NewMultiArrayExpr) {
			allocSite = ESCAPE_NODE;
		}

		// Create this node in the heap, if it doesn't already exist
		newNode(allocSite, 0, new HashSet<>(), null);
		
		boolean isThreadObject = false;
		if(allocSite instanceof NewExpr && ((RefType) ((NewExpr) allocSite).getType()) != null) {
			
			SootClass sootClass1 = ((RefType) ((NewExpr) allocSite).getType()).getSootClass();
			while(true) {
				Chain<SootClass> implementSootClass = sootClass1.getInterfaces();
				Iterator<SootClass> it = implementSootClass.iterator();
				while(it.hasNext()) {
					SootClass sc = it.next();
					if(sc.getName().contains("java.lang.Runnable")) {
						isThreadObject = true;
					}
				}
				
				if(sootClass1.getName().contains("java.lang.Thread")){
					isThreadObject  = true;
				}
				
				if (sootClass1.hasSuperclass()) {
					sootClass1 = sootClass1.getSuperclass();
					
				} else {
					break;
				}
				
			}
		}

		// Assign LHS to the new node
		
		Set<AnyNewExpr> target = new HashSet<AnyNewExpr>();
		if(roots.containsKey(lhs) && roots.get(lhs) != null) {
			target.addAll(roots.get(lhs));
		}
		target.add(allocSite);
		if(isThreadObject) {
			target.add(ESCAPE_NODE);
		}
		roots.put(lhs, Collections.unmodifiableSet(target));

		// Ensure reachability.
		gc();
	}
	
	public void assignReturnVar(Local lhs, Set<AnyNewExpr> targets) {
		Set<AnyNewExpr> newTargets;
		if(roots.get(lhs) != null) {
			newTargets = new HashSet<>(roots.get(lhs));
		}else {
			newTargets = new HashSet<>();
		}
		
		newTargets.addAll(targets);
		roots.put(lhs, Collections.unmodifiableSet(newTargets));

		// Ensure reachability.
		gc();
	}



	public void assignEscape(Local lhs) {
		assignNew(lhs, ESCAPE_NODE);
	}
	
	public void assignPersistent(Local lhs) {
		assignNew(lhs, PERSISTENT_NODE);
	}

	/**
	 * Determines whether an object of one class can be cast to another class.
	 * 
	 * @param fromClass the source type
	 * @param toClass   the target type
	 * @return <tt>true</tt> if and only if <tt>fromClass</tt> is a sub-type of (or
	 *         implements) <tt>toClass</tt>
	 */
	public static boolean canCast(SootClass fromClass, SootClass toClass) {
		// Handle classes and interfaces differently
		
		if (toClass.isInterface()) {
			if(fromClass.toString().equals(toClass.toString())) {
				return true;
			}
			// For interfaces, the fromClass (or one of its super-classes) must
			// implement fromClass
			if (fromClass.implementsInterface(toClass.toString())) {
				return true;
			}

			if (fromClass.getInterfaceCount() > 0) {
				// Check sub interfaces
				for (SootClass subInterface : fromClass.getInterfaces()) {
					if (canCast(subInterface, toClass)) {
						return true;
					}
				}
			}

			if (fromClass.hasSuperclass()) {
				return canCast(fromClass.getSuperclass(), toClass);
			} else {
				return false;
			}
		} else {
			// For classes, the fromClass (or one of its super-classes) and
			// toClass have to be same.
			
			if (fromClass.equals(toClass)) {
				return true;
			} else if (fromClass.hasSuperclass()) {
				return canCast(fromClass.getSuperclass(), toClass);
			} else {
				return false;
			}
		}
	}

	/**
	 * Creates a new node for a constant.
	 */
	private NewExpr constantNewExpr(Constant constant) {
		if (constant instanceof StringConstant) {
			return STRING_SITE;
		} else if (constant instanceof ClassConstant) {
			return CLASS_SITE;
		} else if (constant instanceof NullConstant) {
			return nullObj;
		} else {
			throw new RuntimeException(constant.toString());
		}
	}

	/**
	 * Ensures the given node is in the heap.
	 */
	private void ensureNode(AnyNewExpr node) {
		// WARNING: No fields are added if this is used!
		if (node != null && !heap.containsKey(node))
			heap.put(node, Collections.unmodifiableMap(new HashMap<SootField, Set<AnyNewExpr>>()));
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof PointsToGraph))
			return false;
		PointsToGraph other = (PointsToGraph) obj;
		if (heap == null) {
			if (other.heap != null)
				return false;
		} else if (!heap.equals(other.heap))
			return false;
		if (roots == null) {
			if (other.roots != null)
				return false;
		} else if (!roots.equals(other.roots))
			return false;
		return true;
	}

	/**
	 * Removes all unreachable nodes from the edge sets.
	 */
	public void gc() {
		// Maintain a work-list of (reachable) nodes to process.
		LinkedList<AnyNewExpr> worklist = new LinkedList<AnyNewExpr>();

		// Add all the nodes pointed-to by root variables to the work-list.
		for (Set<AnyNewExpr> nodes : roots.values()) {
			if(nodes != null) {
				worklist.addAll(nodes);
			}
		}

		for(Local x: roots.keySet()) {
			if(roots.get(x) != null) {
				for(AnyNewExpr y: roots.get(x)) {
					if(y == null) {
						System.out.println("local is "+x);
					}
				}
			}
			
		}
		
		// Start with an empty field map (save the old one!)
		Map<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>> oldHeap = this.heap;
		Map<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>> newHeap = new HashMap<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>>();

		// Process work-list.
		while (!worklist.isEmpty()) {
			// Get the next element
			AnyNewExpr node = worklist.remove();

			if (node == nullObj)
				continue;

			// Ignore null pointees from the work-list
			if (node == null) {
				throw new NullPointerException();
			}
				
			// If this is already there in the new map, then ignore (duplicate
			// processing)
			if (newHeap.containsKey(node))
				continue;

			// Otherwise, just get the original stuff back
	
			newHeap.put(node, oldHeap.get(node));

			// Add targets of this node to the work-list.
			if(newHeap.get(node) == null) {
				newHeap.put(node, new HashMap<>());
			}
			for (Set<AnyNewExpr> targets : newHeap.get(node).values()) {
				worklist.addAll(targets);
			}
			

		}

		// Set this heap to the new minimal heap
		this.heap = newHeap;

	}

	/**
	 * Loads a field of an object into a root variable.
	 */
	public void getField(Stmt s, Local lhs, Local rhs, SootField field) {
		// Find whatever the RHS->F was pointing to.
		Set<AnyNewExpr> rhsPointees = roots.get(rhs);
		Set<AnyNewExpr> rhsFieldPointees = new HashSet<AnyNewExpr>();
		
		
		
		for (AnyNewExpr src : rhsPointees) {
			// SHASHIN
			
			
			if (src == nullObj) {
				
				continue;
			}
			// SHASHIN
			if (src == null) {
				throw new NullPointerException();
			} else if (src == PERSISTENT_NODE) {
				rhsFieldPointees.add(PERSISTENT_NODE);
			}
			else if(src == ESCAPE_NODE ) {
				rhsFieldPointees.add(ESCAPE_NODE);
			}else if(PointsToAnalysis.summaryObject.contains(src)) {
				rhsFieldPointees.add(src);
			}
			else if (heap.get(src).containsKey(field)) {
				Set<AnyNewExpr> targets = heap.get(src).get(field);
				rhsFieldPointees.addAll(targets);
			}
			
		}

		// Add the indirect pointees to the LHS edges
		roots.put(lhs, Collections.unmodifiableSet(rhsFieldPointees));

		// Ensure reachability.

		gc();
	
	}
	
	public Set<AnyNewExpr> getField(Local rhs, SootField field) {
		// Find whatever the RHS->F was pointing to.
		Set<AnyNewExpr> rhsPointees = roots.get(rhs);
		Set<AnyNewExpr> rhsFieldPointees = new HashSet<AnyNewExpr>();
		
		for (AnyNewExpr src : rhsPointees) {
			
			if (src == nullObj) {
				
				continue;
			}

			if (src == null) {
				throw new NullPointerException();
			} else if (src == PERSISTENT_NODE) {
				rhsFieldPointees.add(PERSISTENT_NODE);
			}
			else if(src == ESCAPE_NODE) {
				rhsFieldPointees.add(ESCAPE_NODE);
			}else if(PointsToAnalysis.summaryObject.contains(src)) {
				rhsFieldPointees.add(src);
			}
			else if (heap.get(src).containsKey(field)) {
				Set<AnyNewExpr> targets = heap.get(src).get(field);
				rhsFieldPointees.addAll(targets);
			}
			
		}


		// Ensure reachability.

		gc();
		return rhsFieldPointees;
	
	}
	
	
	public Set<AnyNewExpr> getField(AnyNewExpr src, SootField field) {
		// Find whatever the RHS->F was pointing to.
	
		Set<AnyNewExpr> rhsFieldPointees = new HashSet<AnyNewExpr>();
			
			
		if (src == nullObj) {
				
			return rhsFieldPointees;
		}
	
		if (src == null) {
			throw new NullPointerException();
		} else if (src == PERSISTENT_NODE) {
			rhsFieldPointees.add(PERSISTENT_NODE);
		}
		else if(src == ESCAPE_NODE) {
			rhsFieldPointees.add(ESCAPE_NODE);
		}else if(PointsToAnalysis.summaryObject.contains(src)) {
			rhsFieldPointees.add(src);
		}
		else if (heap.get(src).containsKey(field)) {
			Set<AnyNewExpr> targets = heap.get(src).get(field);
			rhsFieldPointees.addAll(targets);
		}
			
		

		// Ensure reachability.

		gc();
		
		return Collections.unmodifiableSet(rhsFieldPointees);
	
	}
	
	
	public Set<SootField> getSootFields(soot.Type t){
		Set<SootField> fields = new HashSet<>();
		if(t instanceof ArrayType) {
			return fields;
		}
			// Find all reference-like fields from the soot class of the new expression
		SootClass sootClass = ((RefType) t).getSootClass();
		while (true) {
			for (SootField field : sootClass.getFields()) {
				if (field.isStatic() == false) { // && field.getType() instanceof RefLikeType) {
					fields.add(field);
				}
			}
			// Get fields for all classes up to java.lang.Object
			if (sootClass.hasSuperclass()) {
				sootClass = sootClass.getSuperclass();
			} else {
				break;
			}
		}
		
		return fields;
	}
	
	

	
	public boolean containsEscapeNode(Local var, SootField field){
		Set<AnyNewExpr> rhsPointees = roots.get(var);
		if(rhsPointees.contains(ESCAPE_NODE) || rhsPointees.contains(PERSISTENT_NODE)) {
			return true;
		}
		for (AnyNewExpr src : rhsPointees) {
			if (src == nullObj) {
				continue;
			}
			if (src == null) {
				throw new NullPointerException();
			}
			else if (heap.containsKey(src) && (heap.get(src).containsKey(ESCAPE_FIELD) || heap.get(src).containsKey(PERSISTENT_FIELD))) {
				return true;
			}
		}
		return false;
		
	}


	/**
	 * Returns the points-to set of a root variable.
	 */
	public Set<AnyNewExpr> getTargets(Local local) {
		if(roots.get(local) == null) {
			return new HashSet<AnyNewExpr>();
		}
		return roots.get(local);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((heap == null) ? 0 : heap.hashCode());
		result = prime * result + ((roots == null) ? 0 : roots.hashCode());
		return result;
	}

	/**
	 * Removes all out-edges of the given variable
	 */
	public void kill(Local v) {
		// Kill the edges
		roots.remove(v);

		// Ensure reachability.
		gc();
	}

	/**
	 * Creates a new node (if it doesn't already exist) in the heap.
	 * @return 
	 * 
	 */
	public void newNode(AnyNewExpr allocSite, int summarizeFields, Set<AnyNewExpr> visited, AnyNewExpr summNode) {
	
		visited.add(allocSite);
		
		
		if (allocSite instanceof AbstractNullObj)
			return;
	

		// OK, we have to create it. Lets find it's fields.
		List<SootField> fields = new LinkedList<SootField>();

		// If we are going to summarise fields later, ensure summary node exists
		if (summarizeFields == 1) {
			newNode(ESCAPE_NODE, 0, visited, null);
		}else if (summarizeFields == 2) {
			newNode(PERSISTENT_NODE, 0, visited, null);
		}else if (summarizeFields == 3) {
			
			HashMap<SootField, Set<AnyNewExpr>> tmpEdge = new HashMap<>();
			HashSet<AnyNewExpr> tmpSet = new HashSet<>(heap.get(summNode).get(SUMMARY_FIELD));
			tmpSet.add(allocSite);
			tmpEdge.put(SUMMARY_FIELD, Collections.unmodifiableSet(tmpSet));
			heap.put(summNode, Collections.unmodifiableMap(tmpEdge));
		}
		

		// First decide properly which type of new expression we have
		if (allocSite instanceof NewExpr) {
			// Enumerate fields only for non-summary nodes
			if (allocSite != PERSISTENT_NODE && allocSite != ESCAPE_NODE && !PointsToAnalysis.summaryObject.contains(allocSite)) {
				// Find all reference-like fields from the soot class of the new expression
				SootClass sootClass = ((RefType) ((NewExpr) allocSite).getType()).getSootClass();
				while (true) {
					for (SootField field : sootClass.getFields()) {
						if (field.isStatic() == false) { // && field.getType() instanceof RefLikeType) {
							fields.add(field);
						}
					}
					// Get fields for all classes up to java.lang.Object
					if (sootClass.hasSuperclass()) {
						sootClass = sootClass.getSuperclass();
					} else {
						break;
					}
				}
			}
			if(PointsToAnalysis.summaryObject.contains(allocSite)) {
				fields.add(SUMMARY_FIELD);
			}
			if(allocSite.getType() != null && allocSite.getType().toString().contains("java.util.")) {
				fields.add(OBJECT_FIELD);
			}
			
			
		} else if (allocSite instanceof NewArrayExpr) {
			// Has only one field: the element[]
			fields.add(ARRAY_FIELD);
		} else if (allocSite instanceof NewMultiArrayExpr) {
			// A multi-dimensional array creation
			// We do not handle multi-arrays right now
			allocSite = ESCAPE_NODE;
		}

		// Create edges
		Map<SootField, Set<AnyNewExpr>> edges = new HashMap<SootField, Set<AnyNewExpr>>();
		for (SootField field : fields) {
			HashSet<AnyNewExpr> targets = new HashSet<AnyNewExpr>();
			if (summarizeFields == 1) {
				targets.add(ESCAPE_NODE);
				edges.put(ESCAPE_FIELD, Collections.unmodifiableSet(targets));
			}else if (summarizeFields == 2) {
				targets.add(PERSISTENT_NODE);
				targets.addAll(heap.get(allocSite).get(field));
				HashSet<AnyNewExpr> tmp = new HashSet<>();
				tmp.add(PERSISTENT_NODE);
				edges.put(PERSISTENT_FIELD, Collections.unmodifiableSet(tmp));
			}else if (summarizeFields == 3) {
				targets.add(summNode);
				targets.addAll(heap.get(allocSite).get(field));
			}
			// Recursively summarize reachable heap.
			if (summarizeFields > 0) {
				Set <AnyNewExpr> oldPointees = this.heap.get(allocSite).get(field);
				if(oldPointees != null) {
					for (AnyNewExpr oldtarget: oldPointees) {
						if(!visited.contains(oldtarget) && oldtarget != PERSISTENT_NODE && oldtarget != ESCAPE_NODE) {
							if(summarizeFields < 3 || !PointsToAnalysis.summaryObject.contains(oldtarget)) {
								visited.add(oldtarget);
								newNode(oldtarget, summarizeFields, visited, summNode);
							}
							
						}	
					}
				}
			}
			edges.put(field, Collections.unmodifiableSet(targets));
		}
		heap.put(allocSite, Collections.unmodifiableMap(edges));
	

	}
	
	
	
	

	/**
	 * Stores values pointed-to by one root variable into a field of objects
	 * pointed-to by another root variable.
	 */
	public void setField(Local lhs, SootField field, Local rhs) {
		
		// You can't set field of a non-existent variable.
		assert_tmp(roots.containsKey(lhs));

		// Since we are doing weak updates, nothing to do if setting field to null
		if (rhs == null)
			return;

		// Find the objects whose field is being modified.
		Set<AnyNewExpr> lhsPointees = roots.get(lhs);
		// Find the objects to which the fields will now point to.
		Set<AnyNewExpr> rhsPointees = roots.get(rhs);
		
		// rshPointees + NullExprObj;

		// LHS variable should exist
		if (lhsPointees == null)
			throw new NullPointerException();

		// RHS variable should exist
		if (rhsPointees == null)
			throw new NullPointerException();

		// If the RHS variable exists, but points to nothing, then bye-bye
		if (rhsPointees.size() == 0) {
			 return;
			// return;
		}

		boolean persistentRhsTargets = false;
		boolean escapeRhsTargets = false;

		


		// For each object that the LHS points to, add to it's field the RHS pointee
		for (AnyNewExpr node : lhsPointees) {
			if (node == null)
				throw new NullPointerException();
			if (node == ESCAPE_NODE) {
				escapeRhsTargets = true;
				continue;
			}else if (node == PERSISTENT_NODE) {
				persistentRhsTargets = true;
				continue;
			}else if(PointsToAnalysis.summaryObject.contains(node)) {
				for(AnyNewExpr rNode: rhsPointees) {
					newNode(rNode, 3, new HashSet<>(), node);
				}
				if(heap.get(node).get(SUMMARY_FIELD).contains(ESCAPE_NODE)) {
					newNode(node, 1, new HashSet<>(), null);
				}
				continue;
			}else if(node == nullObj) {
				continue;
			}
				
			// Add the new edges (copy-and-modify as edges are immutable)
			Map<SootField, Set<AnyNewExpr>> oldEdges = heap.get(node);
			Map<SootField, Set<AnyNewExpr>> newEdges = new HashMap<SootField, Set<AnyNewExpr>>(oldEdges);
			Set<AnyNewExpr> oldTargets = oldEdges.get(field);
			
			if (oldTargets == null) {
				oldTargets = new HashSet<AnyNewExpr>();
			}
			Set<AnyNewExpr> newTargets = new HashSet<AnyNewExpr>(oldTargets);

			boolean change = newTargets.addAll(rhsPointees);
			
			if (change) {
				newEdges.put(field, Collections.unmodifiableSet(newTargets));
				heap.put(node, Collections.unmodifiableMap(newEdges));
			}
		}

		// If the LHS local pointed to SUMMARY, then we must summarize all
		// fields of the RHS pointees as we do not know if any such edge
		// could be created (since we are not maintaining edges out of SUMMARY)
		
		
		
		if (escapeRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 1, new HashSet<>(), null);
			}
		}else if(persistentRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 2, new HashSet<>(), null);
			}
		}
		
		return;
	}

	
	
public void setField(Local lhs, SootField field, Set<AnyNewExpr> rhsSet) {
		
		//System.out.println("setfield inst is " + lhs + "." + field + " = "+rhs);
		// You can't set field of a non-existent variable.
		assert_tmp(roots.containsKey(lhs));

		// Since we are doing weak updates, nothing to do if setting field to null
		if (rhsSet.size() == 0)
			return;

		// Find the objects whose field is being modified.
		Set<AnyNewExpr> lhsPointees = roots.get(lhs);
		// Find the objects to which the fields will now point to.
		Set<AnyNewExpr> rhsPointees = rhsSet;
		// rshPointees + NullExprObj;

		// LHS variable should exist
		if (lhsPointees == null)
			throw new NullPointerException();

		// RHS variable should exist
		if (rhsPointees == null)
			throw new NullPointerException();

		// If the RHS variable exists, but points to nothing, then bye-bye
		if (rhsPointees.size() == 0) {
			 return;
			// return;
		}

		boolean persistentRhsTargets = false;
		boolean escapeRhsTargets = false;

		


		// For each object that the LHS points to, add to it's field the RHS pointee
		for (AnyNewExpr node : lhsPointees) {
			if (node == null)
				throw new NullPointerException();
			if (node == ESCAPE_NODE) {
				escapeRhsTargets = true;
				continue;
			}else if (node == PERSISTENT_NODE) {
				persistentRhsTargets = true;
				continue;
			}else if(PointsToAnalysis.summaryObject.contains(node)) {
				for(AnyNewExpr rNode: rhsPointees) {
					newNode(rNode, 3, new HashSet<>(), node);
				}
				if(heap.get(node).get(SUMMARY_FIELD).contains(ESCAPE_NODE)) {
					newNode(node, 1, new HashSet<>(), null);
				}
				continue;
			}else if(node == nullObj) {
				continue;
			}
				
			// Add the new edges (copy-and-modify as edges are immutable)
			Map<SootField, Set<AnyNewExpr>> oldEdges = heap.get(node);
			Map<SootField, Set<AnyNewExpr>> newEdges = new HashMap<SootField, Set<AnyNewExpr>>(oldEdges);
			Set<AnyNewExpr> oldTargets = oldEdges.get(field);
			
			if (oldTargets == null) {
				oldTargets = new HashSet<AnyNewExpr>();
			}
			Set<AnyNewExpr> newTargets = new HashSet<AnyNewExpr>(oldTargets);

			boolean change = newTargets.addAll(rhsPointees);
			
			if (change) {
				newEdges.put(field, Collections.unmodifiableSet(newTargets));
				heap.put(node, Collections.unmodifiableMap(newEdges));
			}
		}

		// If the LHS local pointed to SUMMARY, then we must summarize all
		// fields of the RHS pointees as we do not know if any such edge
		// could be created (since we are not maintaining edges out of SUMMARY)
		
		
		
		if (escapeRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 1, new HashSet<>(), null);
			}
		}else if(persistentRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 2, new HashSet<>(), null);
			}
		}
		return;
	}

	
	
	/**
	 * Stores a constant into a field of objects pointed-to by a root variable.
	 */
	public void setFieldConstant(Local lhs, SootField field, Constant rhs) {
		// Find out the alloc site of the constant
		NewExpr newExpr = constantNewExpr(rhs);
		// If null, do nothing, as we handle only weak updates,
		// otherwise, add the edge
		if (newExpr != null) {
			setFieldNew(lhs, field, newExpr);
		}
	}

	/**
	 * Stores a new object into a field of objects pointed-to by a root variable.
	 */
	public void setFieldNew(Local lhs, SootField field, AnyNewExpr allocSite) {
		// You can't set field of a non-existent variable.
		assert_tmp(roots.containsKey(lhs));

		// Create this node in the heap, if it doesn't already exist
		newNode(allocSite, 0, new HashSet<>(), null);

		// Find the objects whose field is being modified.
		Set<AnyNewExpr> lhsPointees = roots.get(lhs);
		// Find the objects to which the fields will now point to.
		Set<AnyNewExpr> rhsPointees = new HashSet<AnyNewExpr>();
		rhsPointees.add(allocSite);

		// LHS variable should exist
		if (lhsPointees == null)
			throw new NullPointerException();

		boolean persistentRhsTargets = false;
		boolean escapeRhsTargets = false;

		


		// For each object that the LHS points to, add to it's field the RHS pointee
		for (AnyNewExpr node : lhsPointees) {
			if (node == null)
				throw new NullPointerException();
			if (node == ESCAPE_NODE) {
				escapeRhsTargets = true;
				continue;
			}else if (node == PERSISTENT_NODE) {
				persistentRhsTargets = true;
				continue;
			}else if(PointsToAnalysis.summaryObject.contains(node)) {
				for(AnyNewExpr rNode: rhsPointees) {
					newNode(rNode, 3, new HashSet<>(), node);
				}
				if(heap.get(node).get(SUMMARY_FIELD).contains(ESCAPE_NODE)) {
					newNode(node, 1, new HashSet<>(), null);
				}
				continue;
			}else if(node == nullObj) {
				continue;
			}
				
			// Add the new edges (copy-and-modify as edges are immutable)
			Map<SootField, Set<AnyNewExpr>> oldEdges = heap.get(node);
			Map<SootField, Set<AnyNewExpr>> newEdges = new HashMap<SootField, Set<AnyNewExpr>>(oldEdges);
			Set<AnyNewExpr> oldTargets = oldEdges.get(field);
			
			if (oldTargets == null) {
				oldTargets = new HashSet<AnyNewExpr>();
			}
			Set<AnyNewExpr> newTargets = new HashSet<AnyNewExpr>(oldTargets);

			boolean change = newTargets.addAll(rhsPointees);
			
			if (change) {
				newEdges.put(field, Collections.unmodifiableSet(newTargets));
				heap.put(node, Collections.unmodifiableMap(newEdges));
			}
		}

		// If the LHS local pointed to SUMMARY, then we must summarize all
		// fields of the RHS pointees as we do not know if any such edge
		// could be created (since we are not maintaining edges out of SUMMARY)
		
		
		
		if (escapeRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 1, new HashSet<>(), null);
			}
		}else if(persistentRhsTargets) {
			for(AnyNewExpr rNode: rhsPointees) {
				newNode(rNode, 2, new HashSet<>(), null);
			}
		}

	}

	/**
	 * Stores the summary node into a field of objects pointed-to by a root
	 * variable.
	 */
//	public void setFieldSummary(Local lhs, SootField field) {
//		setFieldNew(lhs, field, SUMMARY_NODE);
//	}

	/**
	 * Removes nodes contained in the argument. This is used at call-edges.
	 */
	public void subtractHeap(PointsToGraph other) {
		for (AnyNewExpr heapNode : other.heap.keySet()) {
			this.heap.remove(heapNode);
		}
	}

	public void summarizeTargetFields(Local lhs, boolean persist) {
		Set<AnyNewExpr> targets = roots.get(lhs);
		if(persist) {
			for (AnyNewExpr allocSite : targets) {
				newNode(allocSite, 2, new HashSet<>(), null);
			}
		}else {
			for (AnyNewExpr allocSite : targets) {
				newNode(allocSite, 1, new HashSet<>(), null);
			}
		}
		
	}

	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();

		for (Local var : roots.keySet()) {
			sb.append(var).append(" -> ");
			for (AnyNewExpr node : roots.get(var)) {
				sb.append(node2String(node)).append(" ");
			}
			sb.append("\n");
		}

		for (AnyNewExpr source : heap.keySet()) {
			for (SootField field : heap.get(source).keySet()) {
				sb.append(node2String(source)).append(".").append(field.isStatic() ? field.toString() : field.getName())
						.append(" -> ");
				for (AnyNewExpr target : heap.get(source).get(field)) {
					sb.append(node2String(target)).append(" ");
				}
				sb.append("\n");
			}
		}

		return sb.toString();
	}

	private String node2String(AnyNewExpr node) {
		if (node == PERSISTENT_NODE) {
			return "PERSISTENT";
		} else if(node == ESCAPE_NODE){
			return "ESCAPE";
		}else if(PointsToAnalysis.summaryObject.contains(node)){
			return "SUMMARY";
		}else if (node == STRING_SITE) {
			return "STRING";
		} else if (node == CLASS_SITE) {
			return "CLASS";
		} else if(node == nullObj) {
			return("NULLL");
		} else if (node == null) {
			return("nahanah");
		}
		else 
		{
			return "[" + node.toString() + " (" + node.hashCode() + ")]";
		}
	}

	

	private String flattenCiToBci(Set<AnyNewExpr> pointees, PointsToAnalysis pta) {
		boolean containsNull = false;
		boolean containsBot = false;
		// a map of all bcis that belong to the same caller index
		Map<Integer, Set<String>> ciToBciMap = new HashMap<Integer, Set<String>>();

		// now we go over the points to set for this var
		for (AnyNewExpr pointee : pointees) {
			// for now, we are only interested in emitting invariants for pure ref objects
			// (no arrays, strings and constants)
//					if (pointee instanceof JNewExpr) {
			// if the JNewExpr node does not exist in the map, then the current variable
			// contains
			// a null in its points-to set
			if (pointee == PointsToGraph.nullObj) {
				containsNull = true;
			} else if (!pta.bciMap2.containsKey(pointee)) {
				containsBot = true;
			} else {
				assert (pta.bciMap2.containsKey(pointee));
				BciContainer pointeeBciContainer = pta.bciMap2.get(pointee);
//						assert (pointeeBciContainer != null);
				Set<String> bciList;
				int pointeeBci = pointeeBciContainer.getBci();
				int pointeeCallerIndex = pointeeBciContainer.getCallerIndex();
				assert (pointeeBci >= 0);
				assert (pointeeCallerIndex > 0);
				
				if(!(pointee.getType() instanceof RefType)) {
					continue;
				}
				assert(pointee.getType() instanceof RefType);
				
				SootClass sc;
				if(pointee.getType() instanceof ArrayType) {
					sc = ((RefType)((ArrayType)pointee).getElementType()).getSootClass();
				}
				else {
					sc = ((RefType) pointee.getType()).getSootClass();
				}
				
				int classIndex;
				if(!pta.sootClassIndices.containsKey(sc)) {
					classIndex = pta.sootClassIndices.size() + 1;
					pta.sootClassIndices.put(sc, classIndex);
				} else {
					//we don't really need the classIndex right now
					classIndex = pta.sootClassIndices.get(sc);
				}
				

				bciList = ciToBciMap.getOrDefault(pointeeCallerIndex, new HashSet<String>());
				bciList.add(String.valueOf(pointeeBci));
				//bciList.add(String.valueOf(pointeeBci) + "-" + String.valueOf(classIndex));
				ciToBciMap.put(pointeeCallerIndex, bciList);
			}
//					}
		}
		// at this point, we have a caller index to bcis map for this variable, along
		// with an indicator that captures whether the variable points to a null object
		// lets proceed to prettify it into a string

		List<String> sList = new ArrayList<String>();
		if(pointees.isEmpty()) {
//			System.out.println("pointees.IsEmpty = true!");
			sList.add("G");
		}
		else if (containsBot) {
			sList.add("G");
		} else {
			for (Integer callerIndex : ciToBciMap.keySet()) {
				StringBuilder sb = new StringBuilder();
				sb.append(callerIndex).append("-");
				sb.append(String.join(".", ciToBciMap.get(callerIndex)));

				sList.add(sb.toString());
			}

			if (containsNull) {
				sList.add("N");
			}
		}

		return String.join(" ", sList);
	}

	public String prettyPrintInvariant5(PointsToAnalysis pta) {
		StringBuilder sbInvariant = new StringBuilder();
		
		//first handle the roots
		// a map to hold the prettified string for each variable
		Map<String, String> varStringMap = new HashMap<String, String>();
		// now go over each variable in the root set
		for (Local var : this.roots.keySet()) {

			// we only care about the local variables (in this version of soot, those are
			// the ones that DO NOT begin with $
			if (var.toString().charAt(0) != '$') {
				String varName = var.toString();
				// a WRONG assumption that all variables with a # are uniquely identified by the
				// LHS substring
				if (var.toString().contains("#")) {
					varName = varName.split("#")[0];
				}

				// this returns a numerical var name, a number that corresponds to its stack
				// slot in bytecode (Don't ask me how!)
				varName = varName.substring(1);

				String str = flattenCiToBci(this.roots.get(var), pta);
				varStringMap.put(varName, String.join(" ", str));
			}

		}
		
		//now do the heap
		
		return sbInvariant.toString();
		
	}
	public String prettyPrintInvariant4(PointsToAnalysis pta, boolean mapArgsOnly, Map<Integer, Local> argsToLocals, boolean mapReturnOnly, 
			boolean normalizeFields) {
		StringBuilder sbInvariant = new StringBuilder();

		// first handle the roots

		// a map to hold the prettified string for each variable
		Map<String, String> varStringMap = new HashMap<String, String>();
		// now go over each variable in the root set
		if(mapArgsOnly) {
			for(Integer argIndex : argsToLocals.keySet()) {
				Local argLocal = argsToLocals.get(argIndex);
				String varName = argLocal.toString();
				assert( varName.charAt(0) != '$') : "assumption that all arg locals are stack vars";
				
				String str = flattenCiToBci(this.roots.get(argLocal), pta);
				
				varStringMap.put(argIndex.toString(), String.join(" ", str));
			}
		} else if (mapReturnOnly) {
			if(this.roots.containsKey(PointsToGraph.RETURN_LOCAL)) {
				String varName = "99";
				String str = flattenCiToBci(this.roots.get(PointsToGraph.RETURN_LOCAL), pta);
			
				varStringMap.put(varName, String.join(" ", str));
			}
		}
			else {
			for (Local var : this.roots.keySet()) {
	
				// we only care about the local variables (in this version of soot, those are
				// the ones that DO NOT begin with $. We also ignore param locals (that start with @)
				if (var.toString().charAt(0) != '$' && var.toString().charAt(0) != '@') {
					String varName = var.toString();
					// a WRONG assumption that all variables with a # are uniquely identified by the
					// LHS substring
					if (var.toString().contains("#")) {
						varName = varName.split("#")[0];
					}
	
					// this returns a numerical var name, a number that corresponds to its stack
					// slot in bytecode (Don't ask me how!)
					varName = varName.substring(1);
	
					String str = flattenCiToBci(this.roots.get(var), pta);
					//there are cases when str is empty, but above call should assign G to such instances
					assert(!str.isEmpty());
					varStringMap.put(varName, String.join(" ", str));
				}
			}
		}

		// then the heap
		// a map to hold the prettified string for each heap object
		// key : ci-bci, value : prettified string
		Map<String, String> objStringMap = new HashMap<String, String>();

		// the heap is keyed by objects, represented by the NewExpr that created them
		for (AnyNewExpr newExpr : this.heap.keySet()) {

			// once again, we only care for purely ref objects (i.e. no array fields,
			// strings)
			if (newExpr instanceof JNewExpr && newExpr != PointsToGraph.STRING_SITE && !PointsToAnalysis.summaryObject.contains(newExpr)
					&& newExpr != PointsToGraph.PERSISTENT_NODE && newExpr != PointsToGraph.ESCAPE_NODE && newExpr != PointsToGraph.CLASS_SITE) {
//				Exception in thread "main" java.lang.AssertionError: new java.lang.Class not found in bciMap2
//				assert (pta.bciMap2.containsKey(newExpr)) : newExpr + " not found in bciMap2";
				BciContainer sourceContainer = pta.bciMap2.get(newExpr);
				if(sourceContainer != null) {
					assert (sourceContainer != null);
					int sourceBci = sourceContainer.getBci();
					int sourceCallerIndex = sourceContainer.getCallerIndex();
					assert (sourceBci >= 0 && sourceCallerIndex > 0);
	
					String objectName = (new StringBuilder()).append(String.valueOf(sourceCallerIndex)).append("-")
							.append(String.valueOf(sourceBci)).toString();
	
					Map<SootField, Set<AnyNewExpr>> fieldsMap = this.heap.get(newExpr);
					Map<String, String> fieldStringMap = new HashMap<String, String>();
					// iterate over the fields for this object
					for (SootField field : fieldsMap.keySet()) {
						// fetch the field name
						String fieldName;
						if(normalizeFields) {
							if(fieldIntMap.containsKey(field)) {
								fieldName = fieldIntMap.get(field).toString();
							} else {
								int index = fieldIntMap.size() + 1;
								fieldIntMap.put(field, index);
								fieldName = String.valueOf(index);
							}
						} else {
							fieldName = field.isStatic() ? field.toString() : field.getName();
						}
						// fetch the points to set of this object and field
						Set<AnyNewExpr> pointees = fieldsMap.get(field);
						// this is a prettified string for this particular field
						String str;
						if(pointees.isEmpty()) {
							str = "N";
						} else {
							str = flattenCiToBci(pointees, pta);
						}
						//TODO: SootField's corresponding to this$0 are sometimes duplicated. Instead of a "put", perform "extend" on the existing element
						if(fieldStringMap.containsKey(fieldName)) {
							String temp;
							temp = fieldStringMap.get(fieldName);
							temp = temp + " " + str;
							fieldStringMap.put(fieldName, temp);
						} else {
							fieldStringMap.put(fieldName, str);
						}
					}
	
					// now we have a map of each field's prettified string
					List<String> sList = new ArrayList<String>();
					for (String fieldName : fieldStringMap.keySet()) {
						StringBuilder sbTemp = new StringBuilder();
						sbTemp.append(fieldName).append(":").append(String.join(" ", fieldStringMap.get(fieldName)));
						sList.add(sbTemp.toString());
					}
	
					if (fieldsMap.size() > 0)
						objStringMap.put(objectName, String.join(",", sList));
	
				}
			} // end instanceof JNewExpr
		}
		
		StringBuilder varString = new StringBuilder();
		List<String> varStringList = new ArrayList<String>();
		for(String var : varStringMap.keySet()) {
			StringBuilder sbTemp = new StringBuilder();
			sbTemp.append(var).append(":");
			sbTemp.append(varStringMap.get(var));
			
			varStringList.add(sbTemp.toString());
		}
		varString.append("(").append(String.join(",", varStringList)).append(")");
		
		StringBuilder heapString = new StringBuilder();
		List<String> fieldStringList = new ArrayList<String>();
		for(String obj : objStringMap.keySet()) {
			StringBuilder sbTemp = new StringBuilder();
			sbTemp.append(obj).append("(").append(objStringMap.get(obj)).append(")");
			
			fieldStringList.add(sbTemp.toString());
		}
		heapString.append("(").append(String.join(",", fieldStringList)).append(")");

		sbInvariant.append(varString).append(heapString);
		
		return sbInvariant.toString();
	}

	public String prettyPrintInvariant3(PointsToAnalysis pta) {
		StringBuilder sbInvariant = new StringBuilder();
		// we want to group by variable (stack slot in our case)
		Map<String, String> varMap = new HashMap<String, String>();

		// for each variable in the rho map
		for (Local var : roots.keySet()) {
			boolean containsNull = false;

			// we only care about the local variables (in this version of soot, those are
			// the ones that DO NOT begin with $
			if (var.toString().charAt(0) != '$') {
				String varName = var.toString();
				// a WRONG assumption that all variables with a # are uniquely identified by the
				// LHS substring
				if (var.toString().contains("#")) {
					varName = varName.split("#")[0];
				}

				// this returns a numerical var name, a number that corresponds to its stack
				// slot in bytecode (Don't ask me how!)
				varName = varName.substring(1);

				// fetch the caller index to bci map
				Map<Integer, Set<String>> ciToBciMap = new HashMap<Integer, Set<String>>();
				for (AnyNewExpr node : roots.get(var)) {
					// if this newexpr is not present in the map, then the current variable has a
					// null assignment
					if (!pta.bciMap2.containsKey(node)) {
						containsNull = true;
					} else {
						// if it exists, then fetch the bci container for this new expr
						BciContainer bciContainer = pta.bciMap2.get(node);
						// some sanity checks
						assert (bciContainer != null);
						assert (bciContainer.getCallerIndex() > 0);
						assert (bciContainer.getBci() >= 0);

						Set<String> bciList = ciToBciMap.getOrDefault(node, new HashSet<String>());
						bciList.add(String.valueOf(bciContainer.getBci()));
						ciToBciMap.put(bciContainer.getCallerIndex(), bciList);
					}
				}
				// at this point, we have a Caller Index to Bcis map for this variable, ready to
				// prettyprint

				List<String> sList = new ArrayList<String>();
				for (Integer callerIndex : ciToBciMap.keySet()) {
					StringBuilder sb = new StringBuilder();
					sb.append(callerIndex).append("-");
					Set<String> bcis = ciToBciMap.get(callerIndex);
					sb.append(String.join(".", bcis));

					sList.add(sb.toString());
				}

				if (containsNull) {
					sList.add("N");
				}
				varMap.put(varName, String.join(" ", sList));

			}
		}

		List<String> l = new ArrayList<String>();
		for (String varName : varMap.keySet()) {
			StringBuilder sb = new StringBuilder();
			sb.append(varName).append(":").append(varMap.get(varName));
			l.add(sb.toString());
		}

		sbInvariant.append("(").append(String.join(",", l)).append(")");

		// now handle the fields
		Map<Integer, String> bciToFieldMap = new HashMap<Integer, String>();
		for (AnyNewExpr source : heap.keySet()) {
			// since we are looking at the heap, we necessarily need to have this available
			if (pta.bciMap2.containsKey(source) && pta.bciMap2.get(source) != null) {

				// assert(pta.bciMap2.containsKey(source));
				BciContainer sourceBCIContainer = pta.bciMap2.get(source);
				int sourceBCI = sourceBCIContainer.getBci();

				StringBuilder fieldRefs = new StringBuilder();

				Map<String, String> fieldsMap = new HashMap<String, String>();
				for (SootField field : heap.get(source).keySet()) {
					Map<Integer, Set<String>> ciToBciMap = new HashMap<Integer, Set<String>>();
					String fieldName = field.isStatic() ? field.toString() : field.getName();

					boolean containsNull = false;
					for (AnyNewExpr node : heap.get(source).get(field)) {
						if (!pta.bciMap2.containsKey(node)) {
							containsNull = true;
						} else {
							BciContainer bciContainer = pta.bciMap2.get(node);
							// some sanity checks
							assert (bciContainer != null);
							assert (bciContainer.getCallerIndex() > 0);
							assert (bciContainer.getBci() >= 0);

							Set<String> bciList = ciToBciMap.getOrDefault(node, new HashSet<String>());
							bciList.add(String.valueOf(bciContainer.getBci()));
							ciToBciMap.put(bciContainer.getCallerIndex(), bciList);

						}
					}

					// at this point, we have a ci to bci map for this field
					List<String> sList = new ArrayList<String>();
					for (Integer callerIndex : ciToBciMap.keySet()) {
						StringBuilder sb = new StringBuilder();
						sb.append(callerIndex).append("-");
						Set<String> bcis = ciToBciMap.get(callerIndex);
						sb.append(String.join(".", bcis));

						sList.add(sb.toString());
					}

					if (containsNull) {
						sList.add("N");
					}
					fieldsMap.put(fieldName, String.join(" ", sList));
					//System.out.println(fieldsMap);

				}

			}

		}

		return sbInvariant.toString();
	}

	// SHASHIN
	public String prettyPrintInvariant2(PointsToAnalysis pta) {
		StringBuilder sbMain = new StringBuilder();
		// Map<String, Set<String>> map = new HashMap<String, Set<String>>();
		Map<String, String> varMap = new HashMap<String, String>();

		// for each variable in the rho map
		for (Local var : roots.keySet()) {
			boolean containsNull = false;
			// we only care about the local variables (in this version of soot, those are
			// the ones that DO NOT begin with $
			if (var.toString().charAt(0) != '$') {
				String varName = var.toString();
				// a WRONG assumption that all variables with a # are uniquely identified by the
				// LHS substring
				if (var.toString().contains("#")) {
					varName = varName.split("#")[0];
				}

				// this returns a numerical var name, a number that corresponds to its stack
				// slot in bytecode (Don't ask me how!)
				varName = varName.substring(1);

				Map<Integer, Set<String>> ciToBciMap = new HashMap<Integer, Set<String>>();
				for (AnyNewExpr node : roots.get(var)) {
					// if the New Expr node does not exist in the map, then the current variable
					// contains a null in its points-to set
					if (!pta.bciMap2.containsKey(node)) {
						containsNull = true;

					} else {
						// if it exists, then fetch the bci container - this gives the bci and the
						// originating method index for the new expr
						BciContainer bciContainer = pta.bciMap2.get(node);
						// sanity checks
						assert (bciContainer != null);
						assert (bciContainer.getCallerIndex() > 0);
						assert (bciContainer.getBci() >= 0);

						Set<String> bciList;
						if (ciToBciMap.containsKey(bciContainer.getCallerIndex())) {
							bciList = ciToBciMap.get(bciContainer.getCallerIndex());
						} else {
							bciList = new HashSet<String>();
						}

						bciList.add(String.valueOf(bciContainer.getBci()));
						ciToBciMap.put(bciContainer.getCallerIndex(), bciList);
					}
				}

				// at this point we have a ciToBciMap for this variable

				List<String> sList = new ArrayList<String>();
				for (Integer callerIndex : ciToBciMap.keySet()) {
					StringBuilder sb = new StringBuilder();
					sb.append(callerIndex).append("-");
					Set<String> bcis = ciToBciMap.get(callerIndex);
					sb.append(String.join(".", bcis));

					sList.add(sb.toString());
				}

				if (containsNull) {
					sList.add("N");
				}
				varMap.put(varName, String.join(" ", sList));

				// sbMain.append("(").append(String.join(".", sList)).append(")");
			}
		}

		List<String> l = new ArrayList<String>();
		for (String varName : varMap.keySet()) {
			StringBuilder sb = new StringBuilder();
			sb.append(varName).append(":").append(varMap.get(varName));
			l.add(sb.toString());
		}

		sbMain.append("(").append(String.join(",", l)).append(")");

		// now do the fields

		for (AnyNewExpr source : heap.keySet()) {

			if (pta.bciMap2.containsKey(source)) {
				BciContainer bciContainer = pta.bciMap2.get(source);
				// sanity checks
				assert (bciContainer != null);
				assert (bciContainer.getCallerIndex() > 0);
				assert (bciContainer.getBci() >= 0);

				int callerIndex = bciContainer.getCallerIndex();
				int bci = bciContainer.getBci();
				StringBuilder tempSb = new StringBuilder();
				tempSb.append(callerIndex).append("-").append(bci);
				tempSb.append("(");

				Map<String, String> fieldMap = new HashMap<String, String>();

				for (SootField field : heap.get(source).keySet()) {
					Map<Integer, Set<String>> ciToBciMap = new HashMap<Integer, Set<String>>();
					String fieldName = field.isStatic() ? field.toString() : field.getName();

				}

				tempSb.append(")");

			}

			// tempSb.append(")");
		}

		return sbMain.toString();
	}

	public String prettyPrintInvariant(PointsToAnalysis pta) {

		StringBuilder sbMain = new StringBuilder();
		Map<String, Set<String>> map = new HashMap<String, Set<String>>();
		for (Local var : roots.keySet()) {
			if (var.toString().charAt(0) != '$') {
				String varName = var.toString();
				if (var.toString().contains("#")) {
					varName = varName.split("#")[0];
				}
				// this returns a numerical var name, which is the stack slot in bytecode
				varName = varName.substring(1);
				Set<String> varMap;
				if (map.containsKey(varName)) {
					varMap = map.get(varName);
				} else
					varMap = new HashSet<String>();

				for (AnyNewExpr node : roots.get(var)) {
					if (pta.bciMap.get(node) == null)
						varMap.add("n");
					else
						varMap.add(pta.bciMap.get(node).toString());
				}

				if (map.containsKey(varName)) {
					map.replace(varName, varMap);
				} else
					map.put(varName, varMap);
			}
		}

		List<String> sList = new ArrayList<String>();
		for (String varName : map.keySet()) {
			StringBuilder sb = new StringBuilder();
			sb.append(varName + ":");
			sb.append(String.join(" ", map.get(varName)));
			sList.add(sb.toString());
		}

		sbMain.append("(").append(String.join(",", sList)).append(")");
		//System.out.println(sbMain.toString());

		map = new HashMap<String, Set<String>>();
		sList = new ArrayList<String>();
		for (AnyNewExpr source : heap.keySet()) {
			for (SootField field : heap.get(source).keySet()) {
				if (pta.bciMap.get(source) != null) {
					StringBuilder tempSb = new StringBuilder();
					tempSb.append(pta.bciMap.get(source)).append(".")
							.append(field.isStatic() ? field.toString() : field.getName());
					tempSb.append(":");

					List<String> tempList = new ArrayList<String>();
					if (heap.get(source).get(field).isEmpty()) {
						tempList.add("n");
					} else {

						for (AnyNewExpr target : heap.get(source).get(field)) {
							if (pta.bciMap.get(target) == null)
								tempList.add("n");
							else
								tempList.add(pta.bciMap.get(target).toString());
						}
					}

					tempSb.append(String.join(" ", tempList));
					sList.add(tempSb.toString());

				}
			}
		}

		sbMain.append("(").append(String.join(",", sList)).append(")");
		
		return sbMain.toString();

	}

	private String node2StringInvariant(AnyNewExpr node) {
		if (node == PERSISTENT_NODE) {
			return "PERSISTENT";
		}else if(node == ESCAPE_NODE) {
			return "ESCAPE";
		}else if(PointsToAnalysis.summaryObject.contains(node)) {
			return "SUMMARY";
		}else if (node == STRING_SITE) {
			return "STRING";
		} else if (node == CLASS_SITE) {
			return "CLASS";
		} else {
			return "[" + node.toString() + " (" + node.hashCode() + ")]";
		}
	}

	/**
	 * Sets this graph to the union of the given arguments.
	 */
	public void union(PointsToGraph p, PointsToGraph q) {
		// Ensure that we are not the operands (otherwise the clear will cause
		// an issue)
		assert_tmp(this != p && this != q);

		// Clear the current data.
		this.roots = new HashMap<Local, Set<AnyNewExpr>>();
		this.heap = new HashMap<AnyNewExpr, Map<SootField, Set<AnyNewExpr>>>();

		// Union root variable edges.
		Set<Local> vars1 = p.roots.keySet();
		Set<Local> vars2 = q.roots.keySet();
		Set<Local> allVars = new HashSet<Local>();
		allVars.addAll(vars1);
		allVars.addAll(vars2);

		for (Local v : allVars) {
			// Collect all pointees
			Set<AnyNewExpr> pointees = new HashSet<AnyNewExpr>();
			if (vars1.contains(v)) {
				if(p.roots.get(v) != null) {
					pointees.addAll(p.roots.get(v));
				}				
			}
			if (vars2.contains(v)) {
				if(q.roots.get(v)!= null) {
					pointees.addAll(q.roots.get(v));
				}
				
			}

			// Add an immutable version of these pointees
			this.roots.put(v, Collections.unmodifiableSet(pointees));
		}

		// Time to union all heap nodes
		Set<AnyNewExpr> nodes1 = p.heap.keySet();
		Set<AnyNewExpr> nodes2 = q.heap.keySet();
		Set<AnyNewExpr> allNodes = new HashSet<AnyNewExpr>();
		allNodes.addAll(nodes1);
		allNodes.addAll(nodes2);

		for (AnyNewExpr node : allNodes) {
			Map<SootField, Set<AnyNewExpr>> edges = new HashMap<SootField, Set<AnyNewExpr>>();

			// First, find all possible fields
			Set<SootField> fields = new HashSet<SootField>();
			if (p.heap.containsKey(node))
				fields.addAll(p.heap.get(node).keySet());
			if (q.heap.containsKey(node))
				fields.addAll(q.heap.get(node).keySet());

			// Now, initialise each field with a mutable set of pointees
			for (SootField field : fields) {
				edges.put(field, new HashSet<AnyNewExpr>());
			}

			// Add field edges from first operand
			if (nodes1.contains(node)) {
				for (SootField field : fields) {
					Set temp = p.heap.get(node).get(field);
					if (temp != null)
						edges.get(field).addAll(temp);
				}
			}

			// Add field edges from second operand
			if (nodes2.contains(node)) {
				for (SootField field : fields) {
					Set temp = q.heap.get(node).get(field);
					if (temp != null)
						edges.get(field).addAll(temp);
				}
			}

			// Immutalize the field edges
			for (SootField field : fields) {
				edges.put(field, Collections.unmodifiableSet(edges.get(field)));
			}

			// Add an immutable version of these edges
			this.heap.put(node, Collections.unmodifiableMap(edges));
		}
	}

	private void assert_tmp(boolean b) {
		if (b == false)
			throw new AssertionError();
	}

	public void killWithoutGC(Local local) {
		roots.remove(local);
	}
	
	
	boolean rhsContainsEscape(Local rhs) {
		ArrayList<AnyNewExpr> worklist = new ArrayList<AnyNewExpr>();
		Set<AnyNewExpr> visited = new HashSet<>();
		if(!this.roots.containsKey(rhs)) {
			return false;
		}

		for(AnyNewExpr temp: this.roots.get(rhs)) {
			visited.add(temp);
			worklist.add(temp);
		}
		if(worklist.contains(ESCAPE_NODE)) {
			return true;
		}
		
		while(!worklist.isEmpty()) {
			AnyNewExpr current = worklist.remove(worklist.size()-1);
			
			if(this.heap.containsKey(current) && this.heap.get(current).containsKey(ESCAPE_FIELD)) {
				return true;
			}
			if(this.heap.containsKey(current)) {
				for(SootField f: this.heap.get(current).keySet()) {
					if(this.heap.get(current).get(f).contains(ESCAPE_NODE)) {
						return true;
					}
					for(AnyNewExpr temp: this.heap.get(current).get(f)) {
						if(!visited.contains(temp) ) {
							visited.add(temp);
							worklist.add(temp);
						}
					}
				}
			}
			
		}
		
		return false;
	}
}