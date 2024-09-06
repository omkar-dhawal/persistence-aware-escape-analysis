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

import soot.options.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.toolkits.callgraph.Edge;
import java.io.PrintStream;

/**
 * A main class for testing call graph construction using a Flow and Context
 * Sensitive Points-to Analysis (FCPA).
 * 
 * <p>Usage: <tt>java vasco.callgraph.CallGraphTest [-cp CLASSPATH] [-out DIR] [-k DEPTH] MAIN_CLASS</tt></p>
 * 
 * @author Rohan Padhye
 */
public class CallGraphTest {
	
	private static String safeDirectory;
	private static String safeArgDirectory;
	private static String outputDirectory;
	private static String inDirectory;
	private static boolean normalizeFields;
	private static long startTime;
	private static long endTime;
	private static boolean limitInSummaries;

	public static void main(String args[]) throws FileNotFoundException {
		
		File file = new File("log.txt");
		int num = 0;
		while(file.exists()) {
			num++;
			file = new File("log"+num+".txt");
			
		}
	      //Instantiating the PrintStream class
	    PrintStream stream = new PrintStream(file);
	    System.out.println("From now on "+file.getAbsolutePath()+" will be your console");
	    System.setOut(stream);
		
		
		outputDirectory = ".";
		String classPath = System.getProperty("java.class.path");
		String mainClass = null;
		int callChainDepth = 10;
		String reflectionLog = null;

		/* ------------------- OPTIONS ---------------------- */
		try {
			int i=0;
			while(true){
				if (args[i].equals("-cp")) {
					classPath = args[i+1];
					i += 2;
				} else if (args[i].equals("-out")) {
					outputDirectory = args[i+1];
					File outDirFile = new File(outputDirectory);
					if (outDirFile.exists() == false && outDirFile.mkdirs() == false) {
						throw new IOException("Could not make output directory: " + outputDirectory);
					}
					File sootifiedFile = new File(outputDirectory + "/sootified");
					if(sootifiedFile.exists() == false && sootifiedFile.mkdirs() == false) {
						throw new IOException("Could not make output directory for sootified classes");
					}
					i += 2;
				} else if(args[i].equals("-in")) {
					inDirectory = args[i+1];
					i += 2;
				} else if (args[i].equals("-k")) { 
					callChainDepth = Integer.parseInt(args[i+1]);
					i += 2;
				} else if (args[i].equals("-reflog")) {
					reflectionLog = args[i+1];
					i += 2;
				} else if (args[i].equals("-safe")) {
					safeDirectory = args[i+1];
					i += 2;
				} else if (args[i].equals("-safeArg")) {
					safeArgDirectory = args[i+1];
					i += 2;
				} else if (args[i].equals("-threshold")) {
					PointsToAnalysis.methodInvocationThreshold = Integer.parseInt(args[i+1]);
					PointsToAnalysis.applyInvocationThreshold = true;
					i += 2;
				} else if(args[i].equals("-dumpAllOuts")) {
					PointsToAnalysis.dumpAllOuts = true;
					File outsFile = new File(outputDirectory + "/all-outs");
					if (outsFile.exists() == false && outsFile.mkdirs() == false) {
						throw new IOException("Could not make output directory for outs");
					}
					i += 1;
					
				} else if(args[i].equals("-normalizeFields")) {
					normalizeFields = true;
					i += 1;
				}	else if(args[i].equals("-limitInSummaries")) {
					limitInSummaries = true;
					i += 1;
				}

				else {
					mainClass = args[i];
					i++;
					break;
				}
			}
			if (i != args.length || mainClass == null)
				throw new Exception();
		} catch (Exception e) {
			System.out.println("Usage: java vasco.callgraph.CallGraphTest [-cp CLASSPATH] [-out DIR] [-k DEPTH] MAIN_CLASS");
			System.exit(1);
		}
		
		
			
		/* ------------------- SOOT OPTIONS ---------------------- */
		String[] sootArgs = {
				"-cp", classPath + ":" + inDirectory, "-pp", 
				//"-src-prec", "J",
				//disable -app here, this will cause all referred classes to be analyzed as library classes - i.e. they won't be transformed
				"-w",
//				"-process-dir", inDirectory,
//				"-x", "soot.*",
//				"-x", "java.*",
//				"-x", "jdk.*",
				//"-no-bodies-for-excluded",
//				"-keep-line-number",
				"-keep-bytecode-offset",
				"-no-bodies-for-excluded",
				//"-p", "cg", "implicit-entry:false",
				//"-p", "cg.spark", "enabled",
				//"-p", "cg.spark", "simulate-natives",
				"-p", "cg.cha", "enabled:true",
//				"-p", "cg.spark", "enabled",
				

//				"-jasmin-backend", 
				"-p", "jb", "preserve-source-annotations:true",
//				"-p", "jb", "stabilize-local-names:true",
				"-p", "jb.ulp", "enabled:false",
				"-p", "jb.dae", "enabled:false",
				"-p", "jb.cp-ule", "enabled:false",
				"-p", "jb.cp", "enabled:false",
				"-p", "jb.lp", "enabled:false",
				//"-p", "jb.lns", "enabled:false",
				"-p", "jb.dtr", "enabled:false",
				"-p", "jb.ese", "enabled:false",
				//"-p", "jb.sils", "enabled:false",
				"-p", "jb.a", "enabled:false",
				"-p", "jb.ule", "enabled:false",
				"-p", "jb.ne", "enabled:false",
//				"-p", "jb.uce", "enabled:false",
				"-p", "jb.tt", "enabled:false",
				
				"-p", "bb.lp", "enabled:false",
				"-p", "jop", "enabled:false",
				"-p", "bop", "enabled:false",
				"-java-version", "1.8",
				
				//"-p", "cg", "safe-forname",
				//"-p", "cg", "safe-newinstance",
				//"-p", "cg", "reflection-log:" + reflectionLog,
				"-include", "org.apache.",
				"-include", "org.w3c.",
				"-exclude", "org.objectweb.asm",
				"-exclude", "soot.asm",
//				"-include", "com.sun.tools.javac.",
				 "-allow-phantom-refs",
				 
//				 "-x", "java",
//				 "-x", "sun",
//				 "-no-bodies-for-excluded",
					
					
				"-main-class", mainClass,
				"-f", "c",
				"-d", outputDirectory + "/sootified", 
				mainClass
		};
		
		System.out.println("Soot args are: " + String.join(" ", sootArgs));
		
		
		
		
		
		
		
		

		/* ------------------- ANALYSIS ---------------------- */
		startTime = System.currentTimeMillis();
		CallGraphTransformer cgt = new CallGraphTransformer(safeDirectory, safeArgDirectory);
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.fcpa", cgt));
		
	    /*PackManager.v().getPack("wjpp").add(new Transform("wjpp.inlineReflCalls", new ReflectiveCallsInliner()));
	    final Scene scene = Scene.v();
	    scene.addBasicClass(Object.class.getName());
	    scene.addBasicClass(SootSig.class.getName(), SootClass.BODIES);
	    scene.addBasicClass(UnexpectedReflectiveCall.class.getName(), SootClass.BODIES);
	    scene.addBasicClass(IUnexpectedReflectiveCallHandler.class.getName(), SootClass.BODIES);
	    scene.addBasicClass(DefaultHandler.class.getName(), SootClass.BODIES);
	    scene.addBasicClass(OpaquePredicate.class.getName(), SootClass.BODIES);
	    scene.addBasicClass(ReflectiveCalls.class.getName(), SootClass.BODIES);*/
	    
//		Scene.v().addBasicClass("avrora.Main", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("java.security.MessageDigestSpi", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("org.dacapo.harness.Avrora", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("sun.net.www.protocol.jar.Handler", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("sun.security.provider.SHA", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.Defaults$AutoProgramReader", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.actions.SimAction", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.monitors.LEDMonitor", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.monitors.PacketMonitor", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.sim.platform.Mica2$Factory", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("avrora.sim.types.SensorSimulation", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("sun.net.www.protocol.jar.Handler", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("sun.security.provider.Sun", SootClass.SIGNATURES);
//		Scene.v().addBasicClass("org.apache.commons.cli.HelpFormatter", SootClass.SIGNATURES);
		Scene.v().addBasicClass("sun.security.util.SecurityConstants",SootClass.BODIES);
//		Scene.v().addBasicClass("java.lang.Object", SootClass.BODIES);
		Scene.v().addBasicClass("java.lang.System",SootClass.BODIES);
		Scene.v().addBasicClass("java.lang.Thread$Caches",SootClass.BODIES);
//		Scene.v().loadNecessaryClasses();
		
	
		Options.v().set_prepend_classpath(true);
		//ReflInliner.main(sootArgs);
		
		soot.Main.main(sootArgs);
		
		PointsToAnalysis pointsToAnalysis = cgt.getPointsToAnalysis();
		
		endTime = System.currentTimeMillis();

		
		/* ------------------- LOGGING ---------------------- */
		try {
			int epf = 0;
			int jpf = 0;
			PrintWriter pw = new PrintWriter(outputDirectory + "/escapeInfo.txt");
			for(Integer methodIndex: PointsToAnalysis.escapingPutField.keySet()) {
				if(!PointsToAnalysis.methodsWithReflection.contains(methodIndex)) {
					if(PointsToAnalysis.escapingPutField.get(methodIndex).contains(-1)) {
						pw.print(methodIndex + "-G ");
						epf += PointsToAnalysis.pfc.get(methodIndex).size();
					}else {
						for(Integer bci: PointsToAnalysis.escapingPutField.get(methodIndex)) {
							pw.print(methodIndex + "-" + bci + " ");
							epf += 1;
						}
					}
				}
				else {
					epf += PointsToAnalysis.pfc.get(methodIndex).size();
					pw.print(methodIndex + "-G ");
				}
			}
		
			
			for(Integer tp: PointsToAnalysis.pfc.keySet()) {
				jpf += PointsToAnalysis.pfc.get(tp).size();
			}
			
			
			System.out.println("escaping putfield number = " + epf);    
			System.out.println("total putfield number = " + jpf);       
			
			pw.close();			
			
		} catch (FileNotFoundException e1) {
			System.err.println("Oops! Could not create log file: " + e1.getMessage());
			System.exit(1);
		}
		
		
		try {
			PrintWriter pMethodIndices = new PrintWriter(outputDirectory + "/mi" + ".txt");
			Map<String, Integer> methodIndices = pointsToAnalysis.methodIndices;
			Map<Integer, String> methodIndicesSorted = new HashMap<Integer, String>();
			for(String key : methodIndices.keySet()) {
				methodIndicesSorted.put(methodIndices.get(key), key);
			}
			for(Integer key : methodIndicesSorted.keySet()) {
				pMethodIndices.println(methodIndicesSorted.get(key));
			}

			pMethodIndices.close();
			int epf = 0;
			int jpf = 0;
			PrintWriter pw1 = new PrintWriter(outputDirectory + "/rhsInfo.txt");
			for(Integer methodIndex: PointsToAnalysis.escapingRhs.keySet()) {
				if(!PointsToAnalysis.methodsWithReflection.contains(methodIndex)) {
					if(PointsToAnalysis.escapingRhs.get(methodIndex).contains(-1)) {
						pw1.print(methodIndex + "-G ");
						epf += PointsToAnalysis.pfc.get(methodIndex).size();
					}else {
						for(Integer bci: PointsToAnalysis.escapingRhs.get(methodIndex)) {
							pw1.print(methodIndex + "-" + bci + " ");
							epf += 1;
						}
					}
				}
				else {
					if(PointsToAnalysis.pfc.containsKey(methodIndex)) {
						epf += PointsToAnalysis.pfc.get(methodIndex).size();
						pw1.print(methodIndex + "-G ");
					}
				}
			}
		
			
			for(Integer tp: PointsToAnalysis.pfc.keySet()) {
				jpf += PointsToAnalysis.pfc.get(tp).size();
			}
			

			
			// System.out.println("bottom escaping = "+PointsToAnalysis.bottom.size());
			System.out.println("escaping rhs number = " + epf);     //98    //107
			System.out.println("total rhs number = " + jpf);        //679   //788
			// System.out.println("total empty rec = " + PointsToAnalysis.emptyRec.size());
			
			pw1.close();

		} catch (FileNotFoundException e1) {
			System.err.println("Oops! Could not create log file: " + e1.getMessage());
			System.exit(1);
		}
		
	}
	
	private static void reportAnalysisTime() throws FileNotFoundException {
		long elapsedTime = endTime - startTime;
		System.out.println(elapsedTime);
		PrintWriter pw = new PrintWriter(outputDirectory + "/stats.txt");
		pw.print(elapsedTime);
		pw.close();
	}
	
	
	public static List<SootMethod> getSparkExplicitEdges(Unit callStmt) {
		Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(callStmt);
		List<SootMethod> targets = new LinkedList<SootMethod>();
		while (edges.hasNext()) {
			Edge edge = edges.next();
			if (edge.isExplicit()) {
				targets.add(edge.tgt());
			}
		}
		return targets;
	}
	
	public static List<SootMethod> getSparkExplicitEdges(SootMethod sootMethod) {
		Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(sootMethod);
		List<SootMethod> targets = new LinkedList<SootMethod>();
		while (edges.hasNext()) {
			Edge edge = edges.next();
			if (edge.isExplicit()) {
				targets.add(edge.tgt());
			}
		}
		return targets;
	}
	
	
	private static Set<SootMethod> dirtyMethods = new HashSet<SootMethod>();
	
	private static void markDirty(Unit defaultSite) {
		List<SootMethod> methods = getSparkExplicitEdges(defaultSite);
		while (methods.isEmpty() == false) {
			SootMethod method = methods.remove(0);
			if (dirtyMethods.contains(method)) {
				continue;
			} else {
				dirtyMethods.add(method);
				methods.addAll(getSparkExplicitEdges(method));
			}
		}
	}
	

	
	
	
}
