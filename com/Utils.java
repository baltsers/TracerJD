/**
 * File: src/com/Utils.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/14/14		hcai		created, miscellaneous utilities
 * 02/13/14		hcai		extended getSuccAfterNextSpecialInvokeStmt to support special treatment for tracing states of a 'specialInvokeStmt'
 * 07/26/14		hcai		gave hands on getting all callees on a call site using Soot Callgraph Builder
*/
package com;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import dua.global.ProgramFlowGraph;
import dua.method.CFGDefUses;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.CFGDefUses.StdVariable;
import dua.method.CFGDefUses.Use;
import dua.method.CFGDefUses.Variable;
import dua.method.ReachableUsesDefs.NodeReachDefsUses;
import dua.util.Pair;
import dua.util.Util;
import fault.StmtMapper;

import profile.UtilInstrum;

import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.ClassConstant;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.CallGraphBuilder;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;
import soot.util.queue.QueueReader;

public class Utils {
	/**
	 * create a local of the particular type <i>t</i> with a unique <i>name</i> as specified in the given body <i>b</i>
	 * ensuring the uniqueness by suffixing, with indefinitely number of trials, a random number 
	 * @param b the body
	 * @param name the name of the target local
	 * @param t the type of the target local
	 * @return the Local created and added
	 */
	public static Local createUniqueLocal(Body b, String name, Type t) {
		String localName = name;
		final Random r = new Random();
		r.setSeed(System.currentTimeMillis());
		do {
			if (null == UtilInstrum.getLocal(b, localName)) {
				// unique name found
				break;
			}
			localName = name + "_" + Math.abs(r.nextInt());
		} while (true);
		
		// create the local with the unique name and add it to tbe body
		Local v = Jimple.v().newLocal(localName, t);
		b.getLocals().add(v);
		return v;
	}
	
	public static Variable makeVariable(Value val, Stmt s) {
		Variable v = null;
		if (val instanceof AnyNewExpr || val instanceof StringConstant || 
				val instanceof ClassConstant || val instanceof InvokeExpr) {
			CFGNode cfgn = ProgramFlowGraph.inst().getNode(s);
			v = new ObjVariable(val, cfgn);
		}
		else {
			v = new StdVariable(val);
		}
		return v;
	}

	/**
	 * dump the Jimple code of the subject project under Soot analysis
	 * @param fObj the target file
	 */
	public static void writeJimple(File fObj) {
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			
			/* traverse all classes */
			Iterator<SootClass> clsIt = Scene.v().getClasses().iterator();
			while (clsIt.hasNext()) {
				SootClass sClass = (SootClass) clsIt.next();
				if ( sClass.isPhantom() ) {
					// skip phantom classes
					continue;
				}
				if ( !sClass.isApplicationClass() ) {
					// skip library classes
					continue;
				}
				
				/* traverse all methods of the class */
				Iterator<SootMethod> meIt = sClass.getMethods().iterator();
				while (meIt.hasNext()) {
					SootMethod sMethod = (SootMethod) meIt.next();
					if ( !sMethod.isConcrete() ) {
						// skip abstract methods and phantom methods, and native methods as well
						continue; 
					}
					if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
						// don't handle reflections now either
						continue;
					}
					
					// cannot instrument method event for a method without active body
					if ( !sMethod.hasActiveBody() ) {
						continue;
					}
					
					//Body body = sMethod.getActiveBody();
					Body body = sMethod.retrieveActiveBody();
					writer.write("\t"+sClass.getName()+"\n");
					writer.write(body + "\n");
				}
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write Jimple file: " + fObj + e); }
		catch (SecurityException e) { System.err.println("Couldn't write Jimple file: " + fObj + e); }
		catch (IOException e) { System.err.println("Couldn't write Jimple file: " + fObj + e); }
	}
	
	public static int getFunctionList(Set<String> mels) {
		/* traverse all classes */
		Iterator<SootClass> clsIt = Scene.v().getClasses().iterator();
		while (clsIt.hasNext()) {
			SootClass sClass = (SootClass) clsIt.next();
			if ( sClass.isPhantom() ) {
				// skip phantom classes
				continue;
			}
			if ( !sClass.isApplicationClass() ) {
				// skip library classes
				continue;
			}
			
			/* traverse all methods of the class */
			Iterator<SootMethod> meIt = sClass.getMethods().iterator();
			while (meIt.hasNext()) {
				SootMethod sMethod = (SootMethod) meIt.next();
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				mels.add(sMethod.getSignature());
			}
		}
		return mels.size();
	}
	/**
	 * dump function list of the subject project under Soot analysis
	 * @param the literal name of the target file
	 */
	public static void dumpFunctionList(String fn) {
		Set<String> mels = new LinkedHashSet<String>();
		if (getFunctionList(mels) < 1) {
			// nothing to dump
			return;
		}
		File fObj = new File(fn);
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			
			for (String m : mels) {
				//writer.write(sClass.getName()+"::"+sMethod.getName()+"\n");
				writer.write(m+"\n");
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (SecurityException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (IOException e) { System.err.println("Couldn't write file: " + fObj + e); }
	}
	
	public static void dumpEntryReachableFunctionList(String fn) {
		File fObj = new File(fn);
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			
			for (SootMethod m : Utils.getReachableMethodsFromEntries(true)) {
				//writer.write(Utils.getFullMethodName(m)+"\n");
				writer.write(m.getSignature()+"\n");
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (SecurityException e) { System.err.println("Couldn't write file: " + fObj + e); }
		catch (IOException e) { System.err.println("Couldn't write file: " + fObj + e); }
	}
	
	/**
	 * a convenient helper determining if the given value is an instance field of "this" object
	 * @param v the value to determine
	 * @param sClass the sootClass the sootField associated with the given value belongs to
	 * @return the decision
	 */
	public static boolean isInstanceVarOfThis(Value v, SootClass sClass) {
		if ( !(v instanceof InstanceFieldRef) ) {
			return false;
		}
		SootField uf = ((FieldRef)v).getField();
		if (!sClass.getFields().contains(uf)) {
			return false;
		}
		Value base = ((InstanceFieldRef)v).getBase();
		if (!base.toString().equalsIgnoreCase("this") ||
				!base.getType().toString().equalsIgnoreCase(sClass.getName()) ) {
			/* not a InstanceFeildRef to the current class's field */
			return false;
		}
		return true;
	}
	
	/**
	 * combine class name and field to produce a name distinguish class fields
	 * @param v a variable that is supposed to be a field reference
	 * @return the canonical name for the field; 
	 * 		- static class variable/class field: className::fieldName
	 * 		- instance variable/class field: className.fieldName
	 */
	public static String getCanonicalFieldName(Variable v) {
		// StdVariable holding a Constant Value is not supported in CFGDefUses for now
		if (v.getValue() instanceof Constant) {
			return v.getValue().toString();
		}
		if (!v.isFieldRef()) {
			return v.toString();
		}
		String fieldName;
		FieldRef fr = (FieldRef)v.getValue();
		if (!fr.getField().isStatic()) {
			assert v.getValue() instanceof InstanceFieldRef;
			fieldName = fr.getField().getDeclaringClass().getName()+".F"+fr.getField().getName();
		}
		else {
			assert v.getValue() instanceof StaticFieldRef;
			fieldName = fr.getField().getDeclaringClass().getName()+"::F"+fr.getField().getName();
		}
		return fieldName;
	}
	
	/**
	 * combine the class name of the declaring class and the method name 
	 * @param m the soot method for which the name is retrieved
	 * @return the full method name that distinguishes the declaring class
	 */
	public static String getFullMethodName(SootMethod m) {
		if (m.isDeclared()) {
			return m.getDeclaringClass().getName() + "::" + m.getName();
		}
		// no declaring class, just use the "global" prefix to indicate that lack 
		return "global::"+m.getName();
	}
	
	/**
	 * a flexible representation of Jimple stmt Id encoded by DUAForensics that is specific to current mcia uses; namely
	 * it could be the id recognizable by DUAF's analysis, or the id encoded by StaticValueTransferGraph's serialization 
	 * which always uses a returnStmt to encode the stmt id that is obtained from the real Stmt in the StaticValueTransferGraph's
	 * graph nodes
	 * @param s the target Jimple statement
	 * @return the Integer representation of the statement id
	 */
	public static Integer getFlexibleStmtId(Stmt s) {
		String sid = "";
		if (null != s) {
			try {
				sid += StmtMapper.getGlobalStmtId(s);
			}
			catch(Exception e) {
				if (s instanceof ReturnStmt && ((ReturnStmt)s).getOp() instanceof IntConstant) {
					/** this is for the makeshift during Serialization of the "Stmt" field of SVTNode ONLY */
					sid += ( (IntConstant) ((ReturnStmt)s).getOp() ).toString();
				}
				else {
					sid = "unknown";
				}
			}
		}
		if (sid.equalsIgnoreCase("unknown") || sid.length() < 1) {
			return -1; // -1 indicates "unknown" or "invalid"
		}
		return Integer.valueOf(sid);
	}
	
	public static boolean isAppConcreteMethod(SootMethod m) {
		if (m.isAbstract()) return false;
		if (!m.isConcrete()) return false;
		//if (!Scene.v().getApplicationClasses().contains(m.getDeclaringClass())) return false;
		if (!getAppMethods().contains(m)) return false;
		return m.toString().indexOf(": java.lang.Class class$") == -1;
	}
	
	/**
	 * retrieve methods that are not control dependent on any methods (or control independent methods - CID methods) 
	 * using the legacy Soot call-graph facilities 
	 * @return the list of entry methods
	 */
	public static List<SootMethod> getCIDMethods(boolean appMethodOnly) {
		List<SootMethod> CIDMethods = new LinkedList<SootMethod>();
		PointsToAnalysis pa = Scene.v().getPointsToAnalysis();//new PAG(new SparkOptions(new LinkedHashMap()));
		CallGraphBuilder cgBuilder = new CallGraphBuilder(pa);
		cgBuilder.build();
		CallGraph cg = cgBuilder.getCallGraph();
		Iterator<MethodOrMethodContext> mIt = cg.sourceMethods();
		while (mIt.hasNext()) {
			SootMethod m = mIt.next().method();
			if (appMethodOnly && !isAppConcreteMethod(m)) {
				// search for application methods only
				continue;
			}
			// methods having no incoming edges are regarded as entry methods
			if (!cg.edgesInto(m).hasNext()) {
				CIDMethods.add(m);
			}
		}
		return CIDMethods;
	}
	
	public static Set<SootMethod> getEntryMethods(boolean appMethodOnly) {
		Set<SootMethod> entryMethods = new LinkedHashSet<SootMethod>();
		for (SootMethod m : EntryPoints.v().all()) {
			if (appMethodOnly && !isAppConcreteMethod(m)) {
				// search for application methods only
				continue;
			}
			entryMethods.add(m);
		}
		return entryMethods;
	}
	
	public static List<SootMethod> getAppMethods() {
		return EntryPoints.v().methodsOfApplicationClasses();
	}
	
	static CallGraph g_cg = null;
	public static List<SootMethod> getCallees(SootMethod caller, Stmt callsite) {
		List<SootMethod> callees = new LinkedList<SootMethod>();
		if (g_cg == null) {
			CallGraphBuilder cgBuilder = new CallGraphBuilder(Scene.v().getPointsToAnalysis());
			cgBuilder.build();
			g_cg = cgBuilder.getCallGraph();
		}
		
		Iterator<Edge> eiter = g_cg.edgesOutOf(callsite);
		while (eiter.hasNext()) {
			Edge curedge = eiter.next();
			assert caller==curedge.src();
			callees.add(curedge.tgt());
		}
		
		return callees;
	}
	
	public static Set<SootMethod> getReachableMethods(SootMethod mSrc, boolean appMethodOnly) {
		Set<SootMethod> reachableMethods = new LinkedHashSet<SootMethod>();
		
		PointsToAnalysis pa = Scene.v().getPointsToAnalysis(); //new PAG(new SparkOptions(new LinkedHashMap()));
		CallGraphBuilder cgBuilder = new CallGraphBuilder(pa);
		
		cgBuilder.build();
		CallGraph cg = cgBuilder.getCallGraph();
		List<MethodOrMethodContext> sources = new LinkedList<MethodOrMethodContext>();
		sources.add(mSrc);
		ReachableMethods rms = new ReachableMethods(cg, sources);
		QueueReader<MethodOrMethodContext> queueReader = rms.listener();
		while (queueReader.hasNext()) {
			SootMethod m = queueReader.next().method();
			if (appMethodOnly && !isAppConcreteMethod(m)) {
				// search for application methods only
				continue;
			}
			
			reachableMethods.add(m);
			rms.update();
		}
				
		return reachableMethods;
	}
	
	public static Set<SootMethod> getReachableMethodsFromEntries(boolean appMethodOnly) {
		Set<SootMethod> reachableMethods = new LinkedHashSet<SootMethod>();
		for (SootMethod m : getEntryMethods(appMethodOnly)) {
			reachableMethods.addAll(getReachableMethods(m, appMethodOnly));
		}
		//Scene.v().getReachableMethods();		
		return reachableMethods;
	}
	
	/**
	 * get the first normal, namely non-Identity unit in the given chain
	 * @param <N> generic element type of the chain
	 * @param chn the given chain in which the search is to perform
	 * @return the first non-ID unit
	 */
	public static <N extends Unit> N getFirstNonIdUnit(Chain<N> chn) {
		N nn = chn.getFirst(); 
		
		while (null != nn && nn instanceof IdentityStmt) {
			nn = chn.getSuccOf(nn);
		}
		return nn;
	}
	
	public static int isUnitInBoxes(List<UnitBox> boxes, Unit u) {
		int loc = -1;
		for (UnitBox ub : boxes) {
			if (ub.getUnit().equals(u)) {
				loc ++;
				break;
			}
		}
		return loc;
	}
	
	public static void dumpUnitGraph(UnitGraph cg) {
		SootMethod sMethod = cg.getBody().getMethod();
		System.out.println("=== the CFG of method " + sMethod + "===");
		
		if (cg.getHeads().size()>1) {
			System.out.println("!!! The complete CFG of method " + sMethod + " has " + cg.getHeads().size() + " heads!!");
		}
		System.out.println("\tHead nodes [size=" + cg.getHeads().size()+"]:");
		for(Unit h: cg.getHeads()) {
			System.out.println("\t\t"+ h);
		}
		Iterator<Unit> iter = cg.iterator();
		while (iter.hasNext()) {
			Unit curu = iter.next();
			System.out.println("\t" + curu + " has " + cg.getSuccsOf(curu).size()+" descendants:");
			for (Unit u : cg.getSuccsOf(curu)) {
				System.out.println("\t\t"+ u + "");
			}
		}
		System.out.println("\tTail nodes [size=" + cg.getTails().size()+"]:");
		for(Unit t: cg.getTails()) {
			System.out.println("\t\t"+ t);
		}
		System.out.println("================ END =========================");
	}
	
	/** adapt to Jimple requirements for instrumenting an access to the given variable (w.r.t its underlying Soot Value */
	public static Value makeBoxedValue(SootMethod m, Value v, List<Object> probe, Type tLocalObj) {
		Body b = m.retrieveActiveBody();
		//Local lobj = UtilInstrum.getCreateLocal(b, "<loc_object>", tLocalObj);
		Local lobj = Utils.createUniqueLocal(b, "<loc_object>", tLocalObj);
		Value vfinal = v;
		if (!(v instanceof Constant || v instanceof Local)) {
			//Local lValCopy = UtilInstrum.getCreateLocal(b, "<loc_box_" + v.getType() + ">", v.getType());
			Local lValCopy = Utils.createUniqueLocal(b, "<loc_box_" + v.getType() + ">", v.getType());
			Stmt sCopyToLocal = Jimple.v().newAssignStmt(lValCopy, v);
			probe.add(sCopyToLocal);
			vfinal = lValCopy;
		}
		
		if (v.getType() instanceof PrimType) {
			Pair<RefType, SootMethod> refTypeAndCtor = Util.getBoxingTypeAndCtor((PrimType) v.getType());
			Stmt sNewBox = Jimple.v().newAssignStmt(lobj,	Jimple.v().newNewExpr(refTypeAndCtor.first()));
			Stmt sInitBox = Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(lobj,refTypeAndCtor.second().makeRef(), vfinal));
			probe.add(sNewBox);
			probe.add(sInitBox);
		} else {
			assert v.getType() instanceof RefLikeType || (v instanceof StaticInvokeExpr);
			Stmt sCopyRef = Jimple.v().newAssignStmt(lobj, vfinal);
			probe.add(sCopyRef);
		}
		
		return lobj;
	}
	public static Value makeBoxedValue(SootMethod m, Value v, List<Object> probe) {
		return makeBoxedValue(m, v, probe, Scene.v().getSootClass("java.lang.Object").getType());
	}
		
	public static Stmt getFirstSafeNonIdStmt(Value val, SootMethod m) {
		return getFirstSafeNonIdStmtFrom(val, m, (Stmt)m.retrieveActiveBody().getUnits().getFirst());
	}
	public static Stmt getFirstSafeNonIdStmtFrom(Value val, SootMethod m, Stmt sFrom) {
		return getFirstSafeNonIdStmtFrom(val, m, sFrom, new HashSet<Object>());
	}
	public static Stmt getFirstSafeNonIdStmtFrom(Value val, SootMethod m, Stmt sFrom, Set<Object> insertedStmts) {
		Body b = m.retrieveActiveBody();
		PatchingChain<Unit> pchain = b.getUnits();
		Stmt s = UtilInstrum.getFirstNonIdStmtFrom(pchain, sFrom);
		/*
		if (m.getName().equals("<init>") && val == b.getLocals().getFirst()) {
			while (s!=null && !(s.containsInvokeExpr() && s.getInvokeExpr() instanceof SpecialInvokeExpr
					&& ((SpecialInvokeExpr) s.getInvokeExpr()).getMethod().getName().equals("<init>") 
					&& ((SpecialInvokeExpr) s.getInvokeExpr()).getBase() == val)) {
				s = (Stmt) pchain.getSuccOf(s);
			}
			if (s!=null) {
				insertedStmts.add(s);
				
				s = (Stmt) pchain.getSuccOf(s);
			}
		}*/
		return s;
	}
	
	public static Stmt getSuccAfterNextSpecialInvokeStmt(PatchingChain<Unit> pchain, Stmt s) {
		return getSuccAfterNextSpecialInvokeStmt(pchain, s, new HashSet<Object>());
	}
	public static Stmt getSuccAfterNextSpecialInvokeStmt(PatchingChain<Unit> pchain, Stmt s, Set<Object> insertedStmts) {
		// if s is new expr, then get past <init> specialinvoke
		if (s instanceof AssignStmt && ((AssignStmt) s).getRightOp() instanceof NewExpr) { // exclude newarray case
				Local lNew = (Local) ((AssignStmt) s).getLeftOp();
				do {
					s = (Stmt) pchain.getSuccOf(s);
				} // get past new expr
				while (	!(s.containsInvokeExpr() && s.getInvokeExpr() instanceof SpecialInvokeExpr 
						&& ((SpecialInvokeExpr) s.getInvokeExpr()).getBase() == lNew));
				
				insertedStmts.add(s);
		}
		return (Stmt) pchain.getSuccOf(s); // get successor, whether s is <init> specialinvoke or not
		/*
		s = (Stmt) pchain.getSuccOf(s);
		while (insertedStmts.contains(s)) {
			s = (Stmt) pchain.getSuccOf(s);
		}
		return s;
		*/
	}
	
	/** directly extracted from DuaF's EH instrumenter */
	public static boolean isParameterUsed(IdentityStmt s, NodeReachDefsUses nRU, SootMethod m) {
		Local lPar = (Local) ((IdentityStmt) s).getLeftOp();
		// ensure that formal param is used
		BitSet bsUIn = nRU.getUBackOut();
		CFGDefUses cfgDU = (CFGDefUses) ProgramFlowGraph.inst().getCFG(m);
		List<Use> uses = cfgDU.getUses();
		final int numUses = uses.size();
		for (int i = 0; i < numUses; ++i) {
			if (bsUIn.get(i) && uses.get(i).getValue() == lPar) {
				return true;
			}
		}
		return false;
	}
	
	public static Stmt getAfterSpecialInvokeStmt(PatchingChain<Unit> pchain, Stmt s) {
		Stmt ret = (s.containsInvokeExpr() && s.getInvokeExpr() instanceof SpecialInvokeExpr) ? (Stmt) pchain.getSuccOf(s) : s;
		if (ret == null) ret = s;
		return ret;
	}
	
	public static boolean isAnonymousName (String name) {
		int idx = name.lastIndexOf('$');
		if (-1 == idx) return false;
		
		String nstr = name.substring(idx+1, name.length()-1); 
		for (Character c : nstr.toCharArray()) {
			if (!Character.isDigit(c)) return false;
		}
	
		return true;
	}
	public static boolean isAnonymousClass (SootClass cls) {
		String clsName = cls.getName();
		return isAnonymousName(clsName);
	}
	
	public static Value makeBoxedVariable(SootMethod m, Variable var, List<Object> probe) {
		return makeBoxedVariable(m, var, probe, Scene.v().getSootClass("java.lang.Object").getType());
	}
	public static Value makeBoxedVariable(SootMethod m, Variable var, List<Object> probe, Type tLocalObj) {
		Value v = var.getValue();
		if (var.isObject()) {
			v = ((ObjVariable)var).getBaseLocal();
		}
		else if (var.isFieldRef() && (v instanceof InstanceFieldRef)) {
			v = ((InstanceFieldRef)v).getBase();
		}
		else if (var.isArrayRef()) {
			v = ((ArrayRef)v).getBase();
		}
		assert v != null;
		//assert !(v instanceof StaticFieldRef);
		return makeBoxedValue(m, v, probe, tLocalObj);
	}
	
	public static int deleteFile(String fname) {
		File fObj = new File(fname);
		try {
			if (fObj.exists() && fObj.isFile()) {
				fObj.delete();
			}
		} 
		catch (SecurityException e) { System.err.println("Couldn't delete file due to security reasons: " + fObj + e); return -2;}
		catch (Throwable e) { System.err.println("Couldn't delete file due to unexpected reason: " + fObj + e); return -1;}
		return 0;
	}
}

/* vim :set ts=4 tw=4 tws=4 */

