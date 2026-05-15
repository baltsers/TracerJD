/**
 * File: src/profile/EventInstrumenter.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/15/14		hcai		created; for instrumenting method- and statement-level events
 * 01/23/14		hcai		added full trace reporter instrumentation at the end of entry methods
 * 02/06/14		hcai		added tracing object ids of heap object's bases, and indice of array elements
 * 02/13/14		hcai		added tracing variable values -- integrating EH instrumentation with the present tracing instrumentation
 * 02/17/14		hcai		fixed a few instrumentation errors (mainly 'negative stack height' and 'expect object/array on stack' errors) (tested with Schedule1 only for now)
 * 02/19/14		hcai		fixed more instrumentation issues and made the working version of EventInstrumenter for NanoXML after for Schedule1
 * 03/04/14		hcai		finally fixed runtime tracing perturbance and  made the whole tracer skeleon working for NanoXML after for Schedule1
 * 03/06/14		hcai		further improved trace instrumenter such that its static analysis module works with XML-security after Schedule1 and NanoXML
 * 03/23/14		hcai		fixed more runtime perturbations from the tracing found with XML-security; added separate blacktype lists for tracing values of used and defined variables
 * 03/28/14		hcai		added static CD information (including normal-branch CDs, virtual-call CDs and exceptional InterCDs)
 * 04/18/14		hcai		added dumping variable ids for post-processing analysis at the end of this static analysis
 * 06/06/14		hcai		fixed array index tracing --- trace the value instead of the variable
 * 06/11/14		hcai		ensured that (1) statementState probes execute after returnInto probe but for call sites only; (2) statementState probes
 * 							for IfStmt and GotoStmt execute prior to, rather than following as for other types of statements, the monitored statement
 * 06/12/14		hcai		added switches for value (all / used-only) tracing
 * 06/13/14		hcai		added static DD information (for return and parameter passing induced dependencies only) 
 * 06/14/14		hcai		added tracing of constant variables (constant return value and constant parameters at call site)
 * 06/15/14		hcai		split statement state probes for call site specially: statement cov and parameter uses before the call and defs
 * 06/18/14		hcai		debugged/tested, and now working, for XML-security after NanoXML and Schedule1: 
 * 							(1) model string constants on return sites---in staticDDinfo; (2) desist treating 'object instantiation statement' ('new Class' but not 'new array') 
 * 							specially---do not jump over the specialinvoke anymore to insert the probe; (3) add the lhs variable from which a specialinvoke on ctor is called as a def
 * 							in addition to being a Use
 * 07/11/14		hcai		label parameter use and return vals to remove the reliance of post-processing on static DDs 
 * 07/12/14		hcai		(1) hoist all use probes of a call site up before the call site and remain def probes after with special treatments for ctor calls;
 * 							(2) desist treating special treatment for 'this' object on identify statement in ctors, which is not necessary now and is driving me crazy as it raises 
 * 								conflicts with the trace structure protocol (the special insertion points will push the probes running into disorder)
 * 07/15/14		hcai		1. import fix: label formal parameter definitions only at the entry of callees (identity statements);
 * 							2. straightforward handling of reflection calls 	
 * 07/17/14		hcai		handled tracing for reflection call sites (in a limited manner for now: only workable for cases in which each argument must be gathered into the 
 * 							argument-array, as is passed to the reflection call, in a different assignment statement from other arguments
 * 07/26/14		hcai		insert method-event probes and probes for parameter/retval passing induced interDDs for, all call sites instead of application calls only, because
 * 							of the difficulties in precisely identifying application callees from library callees on a (esp. virtual) call site
 * 08/07/14		hcai		fixed the bug that disabling the 'value-tracing' option causes failure in tracing base object ids  
 * 08/16/14		hcai		added option for profiling statement execution cost only: when enabled, monitors other than stmtCov will be skipped  	 						     
*/
package profile;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import profile.InstrumManager;

import dua.Extension;
import dua.Forensics;
import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.ReachableUsesDefs;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses;
import dua.method.CFGDefUses.CSArgVar;
import dua.method.CFGDefUses.Def;
import dua.method.CFGDefUses.NodeDefUses;
import dua.method.CFGDefUses.ObjVariable;
import dua.method.CFGDefUses.ReturnVar;
import dua.method.CFGDefUses.Use;
import dua.method.CFGDefUses.Variable;
import dua.method.CallSite;
import dua.method.ReachableUsesDefs.NodeReachDefsUses;
import dua.util.Util;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;
import soot.util.*;

import com.*;

public class EventInstrumenter implements Extension {
	
	protected SootClass clsMonitor;
	
	protected SootMethod mInitialize;
	protected SootMethod mEnter;
	protected SootMethod mReturnInto;
	protected SootMethod mTerminate;
	
	protected SootMethod mStmtCovReporter;
	protected SootMethod mBranchReporter;
	protected SootMethod mStmtStateReporter;
	protected SootMethod mCachedContentReporter;
	
	protected File fJimpleOrig = null;
	protected File fJimpleInsted = null;
	
	protected static boolean bProgramStartInClinit = false;
	protected static StaticOptions opts = new StaticOptions();
	
	private static final Object g_null = NullConstant.v(); // StringConstant.v("null"); // Jimple.NULL;
	
	public static void main(String args[]){
		args = preProcessArgs(opts, args);

		EventInstrumenter eaInst = new EventInstrumenter();
		// examine catch blocks
		dua.Options.ignoreCatchBlocks = false;
		dua.Options.skipDUAAnalysis = true;
		
		Forensics.registerExtension(eaInst);
		Forensics.main(args);
	}
	
	protected static String[] preProcessArgs(StaticOptions _opts, String[] args) {
		opts = _opts;
		args = opts.process(args);
		
		String[] argsForDuaF;
		int offset = 0;

		argsForDuaF = new String[args.length + 2 - offset];
		System.arraycopy(args, offset, argsForDuaF, 0, args.length-offset);
		argsForDuaF[args.length+1 - offset] = "-paramdefuses";
		argsForDuaF[args.length+0 - offset] = "-keeprepbrs";
		
		return argsForDuaF;
	}
	
	/**
	 * Descendants may want to use customized event monitors
	 */
	protected void init() {
		clsMonitor = Scene.v().getSootClass("profile.EventMonitor");
		mStmtCovReporter = clsMonitor.getMethodByName("reportStmtCov");
		mCachedContentReporter = clsMonitor.getMethodByName("dumpCachedStates");
		
		if (opts.stmtExecTimeProfiling()) {
			return;
		}
		
		mInitialize = clsMonitor.getMethodByName("initialize");
		mEnter = clsMonitor.getMethodByName("enter");
		mReturnInto = clsMonitor.getMethodByName("returnInto");
		mTerminate = clsMonitor.getMethodByName("terminate");
		
		mBranchReporter = clsMonitor.getMethodByName("reportBranch");
		mStmtStateReporter = clsMonitor.getMethodByName("reportStmtState");
		
		createVariableIndex();
	}
	
	public void run() {
		System.out.println("Running Tracer-EventInstrumenter extension of DUA-Forensics");
		StmtMapper.getCreateInverseMap();
		
		if (opts.dumpJimple()) {
			fJimpleOrig = new File(Util.getCreateBaseOutPath() + "JimpleOrig.out");
			com.Utils.writeJimple(fJimpleOrig);
		}
		if (opts.dumpFunctionList()) {
			Utils.dumpFunctionList(Util.getCreateBaseOutPath() + "functionList.out");
			//utils.dumpEntryReachableFunctionList(Util.getCreateBaseOutPath() + "functionList.out");
		}
		
		if (!opts.stmtExecTimeProfiling()) {
			if (opts.staticCDInfo()) {
				// compute static control dependencies before inserting any probes
				StaticCDInfo scdinfo = new StaticCDInfo(opts.debugOut());
				scdinfo.turnExceptionalInterCD(true);
				scdinfo.turnIgnoreRTECD(false);
				scdinfo.turnMemoryForSpeed(true);
				scdinfo.SerializeToFile(Util.getCreateBaseOutPath() + "staticCDInfo.dat");
				if (opts.debugOut()) {
					scdinfo.dumpCDMappings(System.out);
				}
			}
			
			/** including these interDDs is mandatory, or the dynamic dependence analysis even for DDs only would be incomplete */
			/* static interDDs for return and parameter passing induced dependencies*/
			/*
			{
				StaticDDInfo sddinfo = new StaticDDInfo(opts.debugOut());
				sddinfo.SerializeToFile(Util.getCreateBaseOutPath() + "staticDDInfo.dat");
				if (opts.debugOut()) {
					sddinfo.dumpDDMappings(System.out);
				}
			}
			*/
			/** do not need static DD anymore but still have to create variables for constants on call sites and return sites */
			StaticDDInfo sddinfo = new StaticDDInfo(opts.debugOut());
			System.out.println("Computer DDInfo: start.");
			sddinfo.computeDDInfo();
			System.out.println("Computer DDInfo: end.");
		}
		
		init();
		
		instrument();
		
		insertCachedContentReporter();
		
		if (opts.dumpJimple()) {
			fJimpleInsted = new File(Util.getCreateBaseOutPath() + "JimpleInstrumented.out");
			com.Utils.writeJimple(fJimpleInsted);
		}
		
		if (!opts.stmtExecTimeProfiling()) {
			dumpVariableIds (new File(Util.getCreateBaseOutPath() + "varIds.out"));
		}
	}
	
	/** List of all variables defined/used statically anywhere */
	private static List<Variable> allVars = new ArrayList<Variable>();
	/** used to index a particular variable in the global list */
	private static Map<Variable,Integer> cacheAllVarsToIds = new LinkedHashMap<Variable, Integer>();
	/** map from statement to constant variables used at the statement */
	private static Map<Stmt, List<Variable>> stmtToConstVars = new LinkedHashMap<Stmt, List<Variable>>();
	
	/** helper for createVariableIndex() */
	public static void addVariableToGlobalIndex(Variable v) {
		Integer vId = cacheAllVarsToIds.get(v);
		if (null == vId) {
			vId = getVarMayEqualAndAlias(allVars, v);
			if (vId==-1) {
				vId = cacheAllVarsToIds.size();
			}
			cacheAllVarsToIds.put(v, vId);
			allVars.add(v);
		}
	}
	public static void addConstantVariableToGlobalIndex(Variable v, Stmt loc) {
		Integer vId = cacheAllVarsToIds.get(v);
		if (null == vId) {
			// do not alias constant variables as they are not discerned by value but by location 
			vId = cacheAllVarsToIds.size();
			cacheAllVarsToIds.put(v, vId);
			allVars.add(v);
	
			List<Variable> convars = stmtToConstVars.get(loc);
			if (null == convars) {
				convars = new ArrayList<Variable>();
				stmtToConstVars.put(loc, convars);
			}
			if (!convars.contains(v)) {
				convars.add(v);
			}
		}
	}
	public static Integer getVariableId(Variable v) {
		return cacheAllVarsToIds.get(v);
	}
	
	/** create the global variable index */
	private static void createVariableIndex() {
		for (CFG cfg : ProgramFlowGraph.inst().getCFGs()) {
			CFGDefUses cfgdu = (CFGDefUses)cfg;
			// local variables
			for (Def d : cfgdu.getDefs()) {
				Variable v = d.getVar();
				addVariableToGlobalIndex(v);
				
				/*
				if (v instanceof CSArgVar) { System.err.println(v + " is a CSArgVar");}
				else if (v instanceof CFGDefUses.CSReturnedVar) {System.err.println(v + " is a CSReturnedVar");}
				*/
			}
			for (Use u : cfgdu.getUses()) {
				Variable v = u.getVar();
				addVariableToGlobalIndex(v);
			}
			
			// field references
			for (Def d : cfgdu.getFieldDefs()) {
				Variable v = d.getVar();
				addVariableToGlobalIndex(v);
			}
			for (Use u : cfgdu.getFieldUses()) {
				Variable v = u.getVar();
				addVariableToGlobalIndex(v);
			}
			
			// array element references
			for (Def d : cfgdu.getArrayElemDefs()) {
				Variable v = d.getVar();
				addVariableToGlobalIndex(v);
			}
			for (Use u : cfgdu.getArrayElemUses()) {
				Variable v = u.getVar();
				addVariableToGlobalIndex(v);
			}
			
			// library objects
			for (Def d : cfgdu.getLibObjDefs()) {
				Variable v = d.getVar();
				addVariableToGlobalIndex(v);
			}
			for (Use u : cfgdu.getLibObjUses()) {
				Variable v = u.getVar();
				addVariableToGlobalIndex(v);
			}
			
			// constant return/parameter
			/** variables from cfgdu.getAllConstDefs() identify a same constant with a unique variable regardless of their various locations
			 * which do not satisfy the need of some post analysis such as slicing 
			 * NOTE: the variable-id mappings for constants will be created in StaticDDInfo's computation
			for (Def d : cfgdu.getAllConstDefs()) {
				Variable v = d.getVar();
				//DEBUG ONLY
				if (v instanceof CSArgVar) {
					System.out.println("Call site constant argument: " + v);
				}
				if (v instanceof ReturnVar) {
					System.out.println("Constant return value: " + v);
				}
				
				addVariableToGlobalIndex(v);
			}
			*/
			
		}
		assert cacheAllVarsToIds.keySet().size() == allVars.size();
		if (opts.debugOut()) {
			System.err.println("DBG: # variables = " + allVars.size());
			Set<Integer> allIds = new TreeSet<Integer>();
			for (Variable v:allVars) {
				allIds.add(cacheAllVarsToIds.get(v));
			}
			System.err.println("DBG: # unique variable ids = " + allIds.size());
		}
	}
	/** adapted from current DuaF's DynSliceInstrumenter */
	private static int getVarMayEqualAndAlias(List<Variable> vars, Variable v) {
		int idx = 0;
		for (Variable vInList : vars) {
			if (vInList.mayEqualAndAlias(v))
				return idx;
			++idx;
		}
		// another possibility: v is an instance-invoke obj var whose base points to "cousin" type of a var in the list
		Value val = v.getValue();
		if (v instanceof ObjVariable && val instanceof InstanceInvokeExpr) {
			idx = 0;
			for (Variable vInList : vars) {
				Value valInList = vInList.getValue();
				if (valInList instanceof InstanceInvokeExpr && ((InstanceInvokeExpr)valInList).getBase() == ((InstanceInvokeExpr)val).getBase()) {
					System.out.println("DBG: in getVarMayEqualAndAlias, found cousin def obj var match of " + v + " and " + vInList + " via base locals");
					return idx;
				}
				++idx;
			}
			//System.out.println("DBG: something wrong in getVarMayEqualAndAlias -- couldn't find cousin def obj var match of " + v + " via base locals in list " + vars);
		}
		// another possibility: v is a returned var and vars has a returned var representative at the end
		if (v instanceof ReturnVar) {
			--idx;
			assert vars.get(idx) instanceof ReturnVar;
			return idx;
		}
		// a final possibility: v is a representative of all actual parameters linked to a formal parameter in the var list
		if (vars.size() == 1 && vars.get(0) instanceof CSArgVar)
			return 0;
		
		return -1;
	}
	
	private int dumpVariableIds(File fObj) {
		try {
			BufferedWriter writer = new BufferedWriter(new FileWriter(fObj));
			List<Integer> vids = new ArrayList<Integer>(new HashSet<Integer>(cacheAllVarsToIds.values()));
			Map<Integer, Variable> idtovar = new LinkedHashMap<Integer, Variable>();
			for (Map.Entry<Variable, Integer> en : cacheAllVarsToIds.entrySet()) {
				idtovar.put(en.getValue(), en.getKey());
			}
			Collections.sort(vids);
			for (Integer vid : vids) {
				writer.write(vid + "\t" + idtovar.get(vid) +"\n");
			}
			writer.flush();
			writer.close();
		}
		catch (FileNotFoundException e) { System.err.println("Couldn't write variable id map: " + fObj + e); return -2;}
		catch (SecurityException e) { System.err.println("Couldn't write variable id map: " + fObj + e); return -2;}
		catch (IOException e) { System.err.println("Couldn't write variable id map: " + fObj + e); return -2;}
		return 0;
	}
	
	/** retrieve the list of constant variables at a return statement or call site for constant return value and constant parameter, respectively */
	List<Variable> getConstantVariables (CFGNode n) {
		List<Variable> convars = new ArrayList<Variable>();
		CallSite cs = n.getCallSite();
		if (null != cs) {
			int startArgIdx = 0;
			if (cs.isInstanceCall()) {	startArgIdx = 1; }
			for(int i=startArgIdx; i<cs.getNumActualParams(); i++) {
				Value aval = cs.getActualParam(i);
				if (aval instanceof Constant) {
					convars.add(new CSArgVar(aval, cs, i));
				}
			}
		}
		else if (n.getStmt() instanceof ReturnStmt && !n.getStmt().getUseBoxes().isEmpty()) {
			Value retv = ((ReturnStmt)n.getStmt()).getOp();
			if (retv instanceof Constant) {
				convars.add(new ReturnVar(retv, n));
			}
		}
		
		return convars;
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           Method-level Event Instrumentation
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
		
	public void instrument() {
		List<SootMethod> entryMes = ProgramFlowGraph.inst().getEntryMethods();
		//List<SootMethod> entryMes = utils.getEntryMethods(true);
		List<SootClass> entryClses = null;
		if (opts.sclinit()) {
			entryClses = new ArrayList<SootClass>();
			for (SootMethod m:entryMes) {
				entryClses.add(m.getDeclaringClass());
			}
		}
		
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
			
			// when there is a static initializer in the entry class, we will instrument the monitor initialize in there instead of the entry method
			boolean hasCLINIT = false;
			if (opts.sclinit()) {
				if (entryClses.contains(sClass)) {
					try {
						SootMethod cl = sClass.getMethodByName("<clinit>");
						hasCLINIT = (cl != null);
					}
					catch (Exception e) {
						// if exception was thrown, either because there are more than one such method (ambiguous) or there is none
						hasCLINIT = (e instanceof RuntimeException && e.toString().contains("ambiguous method"));
					}
				}
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
				
				if (sMethod.getActiveBody().getUnits().size() > 2000) {
					System.err.println(new Exception().getStackTrace()[0].getMethodName() + ": " + 
							sMethod.getSignature() + " skipped because of its oversize.");
					continue;
				}
				
				//Body body = sMethod.getActiveBody();
				Body body = sMethod.retrieveActiveBody();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				//String meId = sClass.getName() +	"::" + sMethod.getName();
				String meId = sMethod.getSignature();
				
				// wrap Try-Catch blocks before instrumenting EA monitors if Required
				if (opts.wrapTryCatch()) {
					TryCatchWrapper.wrapTryCatchAllBlocks(sMethod, opts.statUncaught(), opts.debugOut());
					//TryCatchWrapper.wrapTryCatchBlocks(sMethod, opts.debugOut());
				}
				
				PatchingChain<Unit> pchn = body.getUnits();
				
				if (opts.stmtExecTimeProfiling()) {
					insertStatementMonitors(pchn, sMethod);
					continue;
				}
				
				/* 1. instrument method entry events and program start event */
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				
				if (cfg == null /*|| !cfg.isReachableFromEntry()*/) {
					// skip dead CFG (method)
					if (opts.debugOut()) {
						System.out.println("\nSkipped method unreachable from entry: " + meId + "!");
					}
					continue;
				}
				
				// -- DEBUG
				if (opts.debugOut()) {
					System.out.println("\nNow instrumenting method " + meId + "...");
				}

				/* the first non-Identity-Statement node is right where we instrument method entrance event */
				CFGNode firstNode = cfg.getFirstRealNonIdNode()/*, firstSuccessor = cfgnodes.get(0)*/;
				Stmt firstStmt = firstNode.getStmt();

				List<Stmt> enterProbes = new ArrayList<Stmt>();
				List<StringConstant> enterArgs = new ArrayList<StringConstant>();
				
				boolean bInstProgramStart = false;
				if (opts.sclinit()) {
					bInstProgramStart = (hasCLINIT && sMethod.getName().equalsIgnoreCase("<clinit>")) || (!hasCLINIT && entryMes.contains(sMethod));
					if (!bProgramStartInClinit) {
						bProgramStartInClinit = (hasCLINIT && sMethod.getName().equalsIgnoreCase("<clinit>"));
					}
				}
				else {
					bInstProgramStart = entryMes.contains(sMethod);
				}
				
				// when "-sclinit" option specified, instrument monitor initialize in <clinit> if any, otherwise in entry method
				if ( bInstProgramStart ) {
					// before the entry method executes, the monitor needs be initialized
					List<StringConstant> initializeArgs = new ArrayList<StringConstant>();
					Stmt sInitializeCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr( mInitialize.makeRef(), initializeArgs ));
					enterProbes.add(sInitializeCall);
					
					// -- DEBUG
					if (opts.debugOut()) {
						System.out.println("monitor initialization instrumented at the beginning of Entry method: " + meId);
					}
				} // -- if (entryMes.contains(sMethod))
				
				enterArgs.add(StringConstant.v(meId));
				Stmt sEnterCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mEnter.makeRef(), enterArgs ));
				enterProbes.add(sEnterCall);
				
				// -- DEBUG
				if (opts.debugOut()) {
					System.out.println("monitor enter instrumented at the beginning of application method: " + meId);
				}
				if ( firstStmt != null ) {
					InstrumManager.v().insertBeforeNoRedirect(pchn, enterProbes, firstStmt);
				}
				else {
					InstrumManager.v().insertProbeAtEntry(sMethod, enterProbes);
				}
				
				/* 2. instrument method returned-into events and program termination event */
				// 2.1 normal returns from call sites OUTSIDE any traps (exception catchers) 
				List<CallSite> callsites = cfg.getCallSites();
				int nCandCallsites = 0;
				for (CallSite cs : callsites) {
					if (cs.hasAppCallees() && !cs.isInCatchBlock()) {
						nCandCallsites ++;
					}
				}
				boolean havingFinally = false;
				String bodySource = body.toString();
				if (bodySource.contains("throw") && 
					bodySource.contains(":= @caughtexception") &&
					bodySource.contains("catch java.lang.Throwable from")) {
					// a very naive, probably imprecise but safe, way to determine if there is any finally block in this method
					havingFinally = true;
					if (opts.debugOut()) {
						System.out.println("finally block exists in method: " + meId);
					}
				}
				
				int nCurCallsite = 0;
				for (CallSite cs : callsites) {
					/*
					//if (!cs.hasAppCallees() && !cs.hasLibCallees()) 
					{
						System.out.println("all callees at " + cs); 
						System.err.println(com.Utils.getCallees(sMethod, cs.getLoc().getStmt()));
					}
					*/
					
					//if (!cs.hasAppCallees()) {
					if (cs.getAllCallees().size()<1) {
						// only care about application calls
						continue;
					}
					
					if (cs.isInCatchBlock()) {
						if (opts.debugOut()) {
							System.out.println("[To instrument callsite in a Catch Block]");
						}
					}
					else {
						nCurCallsite ++;
					}
					// -- DEBUG
					if (opts.debugOut()) {
						System.out.println("monitor returnInto instrumented at call site " + cs + " in method: " + meId);
					}
					
					List<Stmt> retinProbes = new ArrayList<Stmt>();
					List<StringConstant> retinArgs = new ArrayList<StringConstant>();
					retinArgs.add(StringConstant.v(meId));
					retinArgs.add(StringConstant.v(/*cs.getLoc().toString()*/cs.hashCode() + ": returnInto after calling " + /*cs.getAppCallees()*/cs.getAllCallees().get(0).getSignature()/*.getName()*/));
					Stmt sReturnIntoCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr( mReturnInto.makeRef(), retinArgs ));
					retinProbes.add(sReturnIntoCall);
					
					InstrumManager.v().insertAfter(pchn, retinProbes, cs.getLoc().getStmt());
				}
				
				// 2.2 catch blocks and finally blocks
				Chain<Trap> traps = body.getTraps();
				// record instrumentation targets to avoid repetitive instrumentation
				Set<Unit> instTargets = new LinkedHashSet<Unit>();
				for (Iterator<Trap> trapIt = traps.iterator(); trapIt.hasNext(); ) {
				    Trap trap = trapIt.next();

				    // instrument at the beginning of each catch block
				    // -- DEBUG
					if (opts.debugOut()) {
						System.out.println("monitor returnInto instrumented at the beginning of catch block " +	trap + " in method: " + meId);
					}
					
					List<Stmt> retinProbes = new ArrayList<Stmt>();
					List<StringConstant> retinArgs = new ArrayList<StringConstant>();
					retinArgs.add(StringConstant.v(meId));
					retinArgs.add(StringConstant.v(/*trap.toString()*/trap.hashCode() + ": returnInto in catch block for " + trap.getException().getName()));
					Stmt sReturnIntoCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mReturnInto.makeRef(), retinArgs ));
					retinProbes.add(sReturnIntoCall);
					
				    //InstrumManager.v().insertBeforeNoRedirect(pchn, retinProbes, (Stmt)trap.getHandlerUnit());
					Stmt instgt = (Stmt)trap.getHandlerUnit();
					if (!instTargets.contains(instgt)) {
						InstrumManager.v().insertAfter (pchn, retinProbes, instgt);
						instTargets.add(instgt);
					}
					
					// instrument at the beginning of each finally block if any
					if (havingFinally) {
						if (trap.getHandlerUnit().equals(trap.getEndUnit())) {
							// we don't need instrument the probes at the same point twice
							// -- note that for a same TRY statement, the beginning of the finally block, which is trap.getEndUnit(),
							// might be equal to the beginning of a catch block
							continue;
						}
						/* whenever there is a finally block for a TRY statement (maybe without any catch block),
						 *   the block will be copied to the end of every trap; So we can just instrument at the end of
						 *   each of these traps to meet the requirement of instrumenting in each finally block
						 */
						List<Stmt> retinProbesF = new ArrayList<Stmt>();
						List<StringConstant> retinArgsF = new ArrayList<StringConstant>();
						retinArgsF.add(StringConstant.v(meId));
						retinArgsF.add(StringConstant.v(/*trap.toString() */trap.getEndUnit().hashCode() + ": returnInto in finally block for " + trap.getException().getName()));
						Stmt sReturnIntoCallF = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr( mReturnInto.makeRef(), retinArgsF ));
						retinProbesF.add(sReturnIntoCallF);
						// -- DEBUG
						if (opts.debugOut()) {
							System.out.println("monitor returnInto instrumented at the beginning of the finally block " + trap.getEndUnit() + " in method: " + meId);
						}
						// again, avoid repetitive instrumentation although it does not affect the algorithm's correctness of EAS
						if (!((Stmt)trap.getEndUnit()).toString().contains(": void returnInto")) {
							InstrumManager.v().insertBeforeRedirect (pchn, retinProbesF, (Stmt)trap.getEndUnit());
						}
					}
				}
				
				// Thus far, we have not insert probe for termination event in the entry method if there is any finally blocks in there
				if (entryMes.contains(sMethod) /*&& havingFinally*/) {
					Set<Stmt> fTargets = new LinkedHashSet<Stmt>();
					for (Unit u : pchn) {  
						Stmt s = (Stmt)u;
						// In Jimple IR, any method has exactly one return statement
						if (dua.util.Util.isReturnStmt(s)) {
							fTargets.add(s);
						}
					}
					
					assert fTargets.size() >= 1;
					for (Stmt tgt : fTargets) {
						List<Stmt> terminateProbe = new ArrayList<Stmt>();
						List<StringConstant> terminateArgs = new ArrayList<StringConstant>();
						String flag =  (dua.util.Util.isReturnStmt(tgt)?"return":"throw") + " statement";
						terminateArgs.add(StringConstant.v("terminate before " + flag));
						Stmt sTerminateCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mTerminate.makeRef(), terminateArgs ));
						terminateProbe.add(sTerminateCall);
						// -- DEBUG
						if (opts.debugOut()) {
							System.out.println("monitor termination instrumented at the end of " + meId + " before " + flag);
						}
						InstrumManager.v().insertBeforeRedirect (pchn, terminateProbe, tgt);
					}
				}
				
				/* here to be inserted per-statement probes, such as those for monitoring def-use, branches and variable address/values, etc. */
				insertStatementMonitors(pchn, sMethod);
			} // -- while (meIt.hasNext()) 
		} // -- while (clsIt.hasNext())
		
		if (opts.dumpJimple()) {
			fJimpleInsted = new File(Util.getCreateBaseOutPath() + "JimpleInstrumented.out");
			Utils.writeJimple(fJimpleInsted);
		}
	
		// important warning concerning the later runs of the instrumented subject
		if (bProgramStartInClinit) {
			System.out.println("\n***NOTICE***: program start event probe has been inserted in EntryClass::<clinit>(), " +
					"the instrumented subject MUST thereafter run independently rather than via EARun!");
		}
	} // -- void instrument
	
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           Statement-level Event Instrumentation
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/** helper function for insertStatementMonitors: label actual parameter and return variable */
	boolean isActualParameter(Value v, CFGNode n, SootMethod m) {
		CallSite cs = n.getCallSite();
		if (null != cs) {
			for (int i=cs.isInstanceCall()?1:0; i <cs.getNumActualParams();++i) {
				if (cs.getActualParam(i).equals(v)) {
					return true;
				}
			}
		}
		return false;
	}
	String getParamRetUseSuffix(Variable v, CFGNode n, SootMethod m) {
		CallSite cs = n.getCallSite();
		//if (null != cs && cs.hasAppCallees()) {
		if (null != cs && cs.getAllCallees().size()>=1) {	
			for (int i=cs.isInstanceCall()?1:0; i <cs.getNumActualParams();++i) {
				boolean bm = false;
				// for Call site argument, argument index needs be matched in addition to the value --- two different args could have equal value but we need to differentiate them
				if ( v instanceof CSArgVar ) {
					bm = v.equals(new CSArgVar(cs.getActualParam(i), cs, i));
				}
				else {
					bm = cs.getActualParam(i).equals(v.getValue());
				}
					
				if (bm) {
					return "&AP%"+i+"@"+n.getStmt().getInvokeExpr().getMethod().getName();
				}
			}
		}
		
		if (!(m.getReturnType() instanceof VoidType) && dua.util.Util.isReturnStmt(n.getStmt())) {
			if ( ((ReturnStmt)n.getStmt()).getOp().equals(v.getValue()) ) {
				return "&RT@"+m.getName();
			}
		}
		return "";
	}
	/** helper function for insertStatementMonitors: label formal parameter and variable to which a returned value is assigned*/
	String getParamRetDefSuffix(Value v, CFGNode n, SootMethod m) {
		ReachableUsesDefs rudcfg = (ReachableUsesDefs) ProgramFlowGraph.inst().getCFG(m);
		/** If we know a method has no any application caller, there is no need to label the formal parameter defs in its entry*/
		/*
		if (rudcfg.getCallerSites().size()<1) {
			System.err.println(m+ " has no application caller");
		}
		else 
		*/
		/** should only label formal parameter variables on the identity statements where they are first declared/defined */
		if (n.getStmt() instanceof IdentityStmt) {
			for (int i=m.isStatic()?0:1; i <rudcfg.getNumFormalParams();++i) {
				if (rudcfg.getFormalParam(i).getV().equals(v)) {
					return "&FP%"+i+"@"+m.getName();
				}
			}
		}
		
		CallSite cs = n.getCallSite();
		//if (null != cs && cs.hasAppCallees() && n.getStmt() instanceof AssignStmt) {
		if (null != cs && cs.getAllCallees().size()>=1 && n.getStmt() instanceof AssignStmt) {	
			if ( ((AssignStmt)n.getStmt()).getLeftOp().equals(v) ) {
				return "&RV@"+n.getStmt().getInvokeExpr().getMethod().getName();
			}
		}
		
		if (hasReflectionCall(n) && n.getStmt() instanceof AssignStmt) {
			if ( ((AssignStmt)n.getStmt()).getLeftOp().equals(v) ) {
				return "&RV@ReflectionInvoke";
			}
		}
		
		return "";
	}
	/** helper function for insertStatementMonitors: identify uses (inside the packed argument list) on reflection call site */ 
	static boolean hasReflectionCall(CFGNode n) {
		CallSite cs = n.getCallSite();
		if (null == cs) return false;
		for (SootMethod ce : cs.getAllCallees()) {
			/** this pattern list might grow in the future but for now we consider this most common case only */
			if (ce.getSignature().contains("<java.lang.reflect.Method: java.lang.Object invoke(java.lang.Object,java.lang.Object[])>"))
				return true;
		}
		return false;
	}
	static Map<Variable, String> addUsesOnReflectionCallsite(CFGNode n, SootMethod m, List<Variable> uses) {
		Map<Variable, String> v2name = new LinkedHashMap<Variable, String>();
		
		// 1. naive way of recognizing reflection call site
		if (!hasReflectionCall(n)) return v2name;
		CallSite cs = n.getCallSite();
		int nAPs = cs.getNumActualParams();
		if (cs.isInstanceCall()) nAPs --;
		if (nAPs != 2) return v2name;
		
		Value args = cs.getActualParam(cs.getNumActualParams()-1);
		if(!(args.getType() instanceof ArrayType)) return v2name;
		
		// 2. collect all 'unique' variables assigned to elements of the array 'args'
		Map<Value, Value> idx2arg = new LinkedHashMap<Value, Value>();
		LinkedList<CFGNode> worklist = new LinkedList<CFGNode>(n.getPreds());
		List<Value> argsAliases = new ArrayList<Value>();
		argsAliases.add(args);
		List<CFGNode> processed = new ArrayList<CFGNode>();
		while (!worklist.isEmpty()) {
			CFGNode pn = worklist.poll();
			if (processed.contains(pn)) continue;
			processed.add(pn);
			worklist.addAll(pn.getPreds());
			
			Stmt ps = pn.getStmt();
			if (!(ps instanceof AssignStmt)) continue; 
			Value lv = ((AssignStmt)ps).getLeftOp();
			Value rv = ((AssignStmt)ps).getRightOp();
			
			if (dua.util.Util.valuesEqual(lv, args, false) || argsAliases.contains(lv)) {
				argsAliases.add(rv);
			}
			if (!(lv instanceof ArrayRef)) continue;
			
			Value base = ((ArrayRef)lv).getBase();
			if (!argsAliases.contains(base) &&
				!Utils.makeVariable(base, ps).mayEqualAndAlias(Utils.makeVariable(args, n.getStmt()))) continue;
			Value idx = ((ArrayRef)lv).getIndex();
			
			
			idx2arg.put(idx, rv);
		}
		
		// this first argument to 'invoke' is not part of the arguments passed to the dynamically invoked method
		//idx2arg.put(IntConstant.v(-1), cs.getActualParam(cs.getNumActualParams()-2));
		
		// 3. label arguments to be passed to the dynamically called method ; also 
		// 	  create constant variables for constant arguments as doing for ordinary application call site
		int idx = idx2arg.size()-(cs.isInstanceCall()?0:1);
		for (Value kv : idx2arg.keySet()) {
			Value vv = idx2arg.get(kv);
			Variable vr;
			if (vv instanceof Constant) {
				vr = new CSArgVar(vv, cs, idx);
				EventInstrumenter.addConstantVariableToGlobalIndex(vr, cs.getLoc().getStmt());
			}
			else {
				vr = Utils.makeVariable(vv, n.getStmt());
			}
			
			if (!uses.contains(vr)) {
				uses.add(vr);
			}
			
			v2name.put(vr, Utils.getCanonicalFieldName(vr)+"&AP#" + idx + "@ReflectionInvoke");
			
			idx --;
		}
			
		return v2name;
	}
	
	/** instrument monitors per statement in the given unit chain */
	int insertStatementMonitors(PatchingChain<Unit> pchn, SootMethod m) {
		List<Unit> allUnits = new ArrayList<Unit>(pchn);
		for (Unit u : allUnits) {
			Stmt s = (Stmt)u;
			
			// Soot does not support instrumenting at identity statements 
			// if (s instanceof IdentityStmt) { continue; }
			
			// skip statements that are inserted rather than in the original code
			CFG cfg = ProgramFlowGraph.inst().getContainingCFG(s);
			if (cfg==null) {continue;}
			CFGNode _n = ProgramFlowGraph.inst().getNode(s);
			if (_n == null) { continue; }
			
			// 1. first, insert statement coverage reporter
			List<Object> stmtCovProbes = new ArrayList<Object>();
			List<Object> stmtCovArgs = new ArrayList<Object>();
			stmtCovArgs.add(IntConstant.v(Utils.getFlexibleStmtId(s)));
			Stmt stmtCovCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtCovReporter.makeRef(), stmtCovArgs ));
			stmtCovProbes.add(stmtCovCall);
			
			if (opts.stmtExecTimeProfiling()) {
				Stmt actualtgt = UtilInstrum.getFirstNonIdStmtFrom(pchn, s);
				InstrumManager.v().insertBeforeRedirect(pchn, stmtCovProbes, actualtgt);
				continue;
			}

			// def-use
			
			// 2. second, insert variable probe for each defined and used variable at statement s
			List<Object> defProbes = new ArrayList<Object>();
			
			NodeDefUses n = (NodeDefUses)_n;
			List<Variable> defs = n.getDefinedVars();
			
			if (s instanceof InvokeStmt && s.toString().contains("<init>")) {
				//System.out.println("let me check: defined vars at " + s + " :" + defs);
				if (s.containsInvokeExpr() && s.getInvokeExpr() instanceof SpecialInvokeExpr) {
					Value lv = ((SpecialInvokeExpr) s.getInvokeExpr()).getBase();
					Variable ld = Utils.makeVariable(lv, s);
					/** As checked, duaf does not treat the object instance from which the specialinvoke of ctor is 
					 * called as a defined variable but semantically we should take it as defined! 
					 * note: it remains as a Use, whose last Def will be either at a formal parameter id-stmt 
					 * or, mostly, the lhs of the new statement
					 */
					assert !defs.contains(ld);
					defs.add ( ld );
				}
			}
			
			for (Variable vd:defs) {
				//List<Object> defProbes = new ArrayList<Object>();
				List<Object> defArgs = new ArrayList<Object>();
				String vname = Utils.getCanonicalFieldName(vd);
				vname += getParamRetDefSuffix(vd.getValue(), n, m);
				// 2.1 for locals
				if (vd.getValue() instanceof Local) {
					Integer vid = cacheAllVarsToIds.get(vd); // System.identityHashCode(vd.getValue())
					assert vid != null;
					defArgs.add(IntConstant.v(vid));
					defArgs.add(StringConstant.v(vname));
					if (s instanceof IdentityStmt && !Utils.isParameterUsed((IdentityStmt)s, (NodeReachDefsUses)n, m)) {
						// it is not only unnecessary but also detrimental to 'monitor' the value of an 'unused' parameter
						defArgs.add(g_null);
					}
					else {
						// always provide options to bypass particular types of objects that are of either disinterest or even harm
						if (opts.notracingval() || opts.defblacktypes().contains(vd.getValue().getType().toString())) {
							defArgs.add(g_null);
						}
						else {
							if (s instanceof AssignStmt && ((AssignStmt) s).getRightOp() instanceof NewExpr) {
								// do not pass the defined variable (object) that is not instantiated yet, which is okay because 
								// 1. it is a local, thus base id must be 0; 2. its value will be the same as the one after the initialization 
								// --- in fact, even we capture its value, we can only to do that after the specialinvoke (on its ctor)
								defArgs.add(g_null);
							}
							else {
								if (m.getName().equals("<init>") && vd.getValue() == m.retrieveActiveBody().getLocals().getFirst() &&
										s instanceof IdentityStmt) {
									// do not pass over the specialinvoke for 'this' object in ctor on this IdStmt either since there is no valid value to be traced here
									defArgs.add(g_null);
								}
								else {
									defArgs.add( com.Utils.makeBoxedValue(m, vd.getValue(), defProbes) );
								}
							}
						}
					}
					//defArgs.add(IntConstant.v(0)); // placeholder for base object id
					defArgs.add(g_null); // placeholder for base object
					//defArgs.add(StringConstant.v("")); // placeholder for array element index
					defArgs.add(g_null); // placeholder for array element index
					//defArgs.add(Utils.makeBoxedVariable(ProgramFlowGraph.inst().getContainingMethod(s), vd, defProbes));
					Stmt defCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), defArgs ));
					defProbes.add(defCall);
					//insertProbe(pchn, defProbes, s, vd.getValue());
					continue;
				}
				
				// 2.2 for field reference
				if (vd.getValue() instanceof FieldRef) {
					Integer vid = cacheAllVarsToIds.get(vd);
					assert vid != null;
					FieldRef fr = (FieldRef) vd.getValue();
					// Integer baseid = 0;
					Object baseobj = null;
					if (!fr.getField().isStatic()) {
						assert fr instanceof InstanceFieldRef;
						// static field does not have base object/instance
						//baseid = System.identityHashCode( ((InstanceFieldRef)fr).getBase() );
						baseobj = ((InstanceFieldRef)fr).getBase();
					}
					defArgs.add(IntConstant.v(vid));
					defArgs.add(StringConstant.v(vname));
					boolean allset=false;
					if (m.getName().equals("<init>")) {
						if (fr.getFieldRef().name().equals("this$0")) {
							allset = true;
						}
						else {
							SootClass cls = fr.getField().getDeclaringClass(); 
							if (cls.getName().equalsIgnoreCase(m.getDeclaringClass().getName()) && Utils.isAnonymousClass(cls)) {
								if (!fr.getField().isDeclared() || fr.getFieldRef().name().startsWith("val$")) {
									allset = true;
								}
							}
						}
					}
					else if (m.getName().equals("<clinit>") && fr.getFieldRef().name().equals("class$0")) {
						allset = true;
					}
					
					if (opts.notracingval() || opts.defblacktypes().contains(vd.getValue().getType().toString())) {
						defArgs.add(g_null);
					}
					else {
						if (!allset) {
							defArgs.add( com.Utils.makeBoxedValue(m, vd.getValue(), defProbes) );
						}
						else {
							defArgs.add(g_null);
						}
					}
					//defArgs.add(IntConstant.v(baseid));
					if (baseobj == null || allset) {
						defArgs.add(g_null);
					}
					else {
						defArgs.add( com.Utils.makeBoxedValue(m, (Value)baseobj, defProbes) );
					}
					
					//defArgs.add(StringConstant.v("")); // placeholder for array element index
					defArgs.add(g_null); // placeholder for array element index
					Stmt defCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), defArgs ));
					defProbes.add(defCall);
					//insertProbe(pchn, defProbes, s, vd.getValue());
					continue;
				}
				
				// 2.3 for array element reference
				if (vd.getValue() instanceof ArrayRef) {
					Integer vid = cacheAllVarsToIds.get(vd);
					assert vid != null;
					ArrayRef ar = (ArrayRef) vd.getValue();
					//Integer baseid = System.identityHashCode (ar.getBase());
					Object baseobj = ar.getBase();
					Value aridx = ar.getIndex();
					defArgs.add(IntConstant.v(vid));
					defArgs.add(StringConstant.v(vname));
					if (s instanceof AssignStmt && ((AssignStmt) s).getRightOp() instanceof NewArrayExpr) {
						// we won't need capture this type of value anyway
						defArgs.add( g_null );
					}
					else {
						if (opts.notracingval() || opts.defblacktypes().contains(vd.getValue().getType().toString())) {
							defArgs.add(g_null);
						}
						else {
							defArgs.add( com.Utils.makeBoxedValue(m, vd.getValue(), defProbes) );
						}
					}
					//defArgs.add(IntConstant.v(baseid));
					defArgs.add( com.Utils.makeBoxedValue(m, (Value)baseobj, defProbes) );
					/*defArgs.add(StringConstant.v( (aridx instanceof Constant?"I":"") + aridx ));*/
					defArgs.add( com.Utils.makeBoxedValue(m, aridx, defProbes) );
					Stmt defCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), defArgs ));
					defProbes.add(defCall);
					//insertProbe(pchn, defProbes, s, vd.getValue());
					continue;
				}
				
				// 2.4 library object
				if (vd.isObject()) {
					Integer vid = cacheAllVarsToIds.get(vd);
					assert vid != null;
					defArgs.add(IntConstant.v(vid));
					defArgs.add(StringConstant.v(vname));
					// if (vd.getValue() instanceof StaticInvokeExpr || vd.getValue() instanceof SpecialInvokeExpr) {
					if (vd.getValue() instanceof InvokeExpr) {	
						// we won't need capture this type of value
						defArgs.add(g_null);
					}
					else {
						if (opts.notracingval() || opts.defblacktypes().contains(vd.getValue().getType().toString())) {
							defArgs.add(g_null);
						}
						else {
							if (vd.isStrConstObj()) {
								defArgs.add( vd.getValue() /*StringConstant.v( ((StringConstant)vd.getValue()).value )*/ );
							}
							else {
								if (vd.getValue() instanceof NewExpr) {
									// the lhs of a 'NewExpr' cannot be accessed before its 'specialInvoke' on the object's initializer is called : accessing it will cause
									// 'expect object/array on stack' VerifyErrors at runtime
									defArgs.add(g_null); 
								}
								else {
									defArgs.add( com.Utils.makeBoxedValue(m, vd.getValue(), defProbes) );
								}
								// defArgs.add( com.Utils.makeBoxedValue(m, vd.getValue(), defProbes) );
							}
						}
					}
					//defArgs.add(IntConstant.v(System.identityHashCode(vd.getValue())));
					defArgs.add(g_null); // placeholder for base object
					//defArgs.add(StringConstant.v("")); // placeholder for array element index
					defArgs.add(g_null); // placeholder for array element index
					Stmt defCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), defArgs ));
					defProbes.add(defCall);
					//insertProbe(pchn, defProbes, s, vd.getValue());
					continue;
				}
				/*
				if (vd.isConstant()) {
					// no need to trace this type of variables
					continue;
				}
				*/
				
				assert false; // should never get here
				
			}
			
			List<Object> useProbes = new ArrayList<Object>();
			// probes for parameter uses at call site need always be placed before the call!
			// also, uses at a in-place-update statement (e.g., $r1=$r1+$r2) must be reported before the statement
			//List<Object> paraUseProbes = new ArrayList<Object>();
						
			List<Variable> uses = n.getUsedVars();
			// constant parameters and constant returns should be traced too
			/*
			CFGDefUses cfgdu = (CFGDefUses)cfg;
			for (Def d : cfgdu.getAllConstDefs()) {
				if (d.getN().getStmt() == s) uses.add(d.getVar());
			}
			*/
			if (stmtToConstVars.containsKey(s)) {
				//uses.addAll(stmtToConstVars.get(s));
				for (Variable _v : stmtToConstVars.get(s)) {
					if (!uses.contains(_v)) uses.add(_v);
				}
			}
			
			/** preliminary handling of reflection calls */
			Map<Variable, String> v2name = addUsesOnReflectionCallsite(n, m, uses);
			
			for (Variable vu:uses) {
				//List<Object> useProbes = new ArrayList<Object>();
				List<Object> useArgs = new ArrayList<Object>();
				String vname = Utils.getCanonicalFieldName(vu);
				vname += getParamRetUseSuffix(vu, n, m);
				if (hasReflectionCall(n) && v2name.containsKey(vu)) {
					vname = v2name.get(vu);
				}
				
				// 2.1 for locals
				if (vu.getValue() instanceof Local || (vu.isConstant() && !vu.isStrConstObj())) {
					Integer vid = cacheAllVarsToIds.get(vu); // System.identityHashCode(vu.getValue())
					assert vid != null;
					useArgs.add(IntConstant.v(-1*vid)); // negative vid indicates variable use as opposed to variable definition
					useArgs.add(StringConstant.v(vname));
					if (opts.notracingusedval() || opts.useblacktypes().contains(vu.getValue().getType().toString())) {
						useArgs.add(g_null);
					}
					else {
						/** a variable of array (not arrayRef--array element) type won't give meaningful value */
						if (vu.getValue().getType() instanceof ArrayType) {
							useArgs.add(g_null);
						}
						else {
							useArgs.add( com.Utils.makeBoxedValue(m, vu.getValue(), useProbes) );
						}
					}
					//useArgs.add(IntConstant.v(0)); // placeholder for base object id
					useArgs.add(g_null); // placeholder for base object
					//useArgs.add(StringConstant.v("")); // placeholder for array element index
					useArgs.add(g_null); // placeholder for array element index
					//useArgs.add(Utils.makeBoxedVariable(ProgramFlowGraph.inst().getContainingMethod(s), vd, useProbes));
					Stmt useCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), useArgs ));
					if (dua.util.Util.isCtorCall(s) && !isActualParameter(vu.getValue(), n, m)) {
						// for safety, the used object from which a ctor is called should be monitored after the ctor is called, so be treated as a 'def'
						defProbes.add(0,useCall); // insert at the head for, again, observing the protocol of "use (execute first) it for a def"
					}
					else {
						useProbes.add(useCall);
					}
					//insertProbe(pchn, useProbes, s, vu.getValue());
					continue;
				}
				
				// 2.2 for field reference
				if (vu.getValue() instanceof FieldRef) {
					Integer vid = cacheAllVarsToIds.get(vu);
					assert vid != null;
					FieldRef fr = (FieldRef) vu.getValue();
					//Integer baseid = 0;
					Object baseobj = null;
					if (!fr.getField().isStatic()) {
						// static field does not have base object/instance
						//baseid = System.identityHashCode( ((InstanceFieldRef)fr).getBase() );
						baseobj = ((InstanceFieldRef)fr).getBase();
					}
					useArgs.add(IntConstant.v(-1*vid)); // negative vid indicates variable use as opposed to variable definition
					useArgs.add(StringConstant.v(vname));
					boolean allset=false;
					if (m.getName().equals("<init>")) {
						if (fr.getFieldRef().name().equals("this$0")) {
							allset = true;
						}
						else {
							SootClass cls = fr.getField().getDeclaringClass(); 
							if (cls.getName().equalsIgnoreCase(m.getDeclaringClass().getName()) && Utils.isAnonymousClass(cls)) {
								if (!fr.getField().isDeclared() || fr.getFieldRef().name().startsWith("val$")) {
									allset = true;
								}
							}
						}
					}
					else if (m.getName().equals("<clinit>") && fr.getFieldRef().name().equals("class$0")) {
						allset = true;
					}
					
					if (opts.notracingusedval() || opts.useblacktypes().contains(vu.getValue().getType().toString())) {
						useArgs.add(g_null);
					}
					else {
						if (!allset) {
							//if (vu.getValue().toString().contains("next")) useArgs.add(g_null); else
							useArgs.add( com.Utils.makeBoxedValue(m, vu.getValue(), useProbes) );
						}
						else {
							useArgs.add(g_null);
						}
					}
					//useArgs.add(IntConstant.v(baseid));
					if (baseobj == null || allset) {
						useArgs.add( g_null );
					}
					else {
						useArgs.add( com.Utils.makeBoxedValue(m, (Value)baseobj, useProbes) );
					}
					//useArgs.add(StringConstant.v("")); // placeholder for array element index
					useArgs.add(g_null); // placeholder for array element index
					Stmt useCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), useArgs ));
					if (dua.util.Util.isCtorCall(s) && !isActualParameter(vu.getValue(), n, m)) {
						// for safety, the used object from which a ctor is called should be monitored after the ctor is called, so be treated as a 'def'
						defProbes.add(0,useCall);
					}
					else {
						useProbes.add(useCall);
					}
					//insertProbe(pchn, useProbes, s, vu.getValue());
					continue;
				}
				
				// 2.3 for array element reference
				if (vu.getValue() instanceof ArrayRef) {
					Integer vid = cacheAllVarsToIds.get(vu);
					assert vid != null;
					ArrayRef ar = (ArrayRef) vu.getValue();
					//Integer baseid = System.identityHashCode (ar.getBase());
					Value baseobj = ar.getBase();
					Value aridx = ar.getIndex();
					useArgs.add(IntConstant.v(-1*vid)); // negative vid indicates variable use as opposed to variable definition
					useArgs.add(StringConstant.v(vname));
					if (s instanceof AssignStmt && ((AssignStmt) s).getRightOp() instanceof NewArrayExpr) {
						// we won't need capture this type of value anyway
						useArgs.add( g_null );
					}
					else {
						if (opts.notracingusedval() || opts.useblacktypes().contains(vu.getValue().getType().toString())) {
							useArgs.add(g_null);
						}
						else {
							useArgs.add( com.Utils.makeBoxedValue(m, vu.getValue(), useProbes) );
						}
					}
					//useArgs.add(IntConstant.v(baseid));
					useArgs.add( com.Utils.makeBoxedValue(m, baseobj, useProbes) );
					/*useArgs.add(StringConstant.v( (aridx instanceof Constant?"I":"") + aridx ));*/
					useArgs.add( com.Utils.makeBoxedValue(m, aridx, useProbes) );
					Stmt useCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), useArgs ));
					if (dua.util.Util.isCtorCall(s) && !isActualParameter(vu.getValue(), n, m)) {
						// for safety, the used object from which a ctor is called should be monitored after the ctor is called, so be treated as a 'def'
						defProbes.add(0,useCall);
					}
					else {
						useProbes.add(useCall);
					}
					//insertProbe(pchn, useProbes, s, vu.getValue());
					continue;
				}
				
				// 2.4 library object
				if (vu.isObject()) {
					Integer vid = cacheAllVarsToIds.get(vu);
					assert vid != null;
					useArgs.add(IntConstant.v(-1*vid)); // negative vid indicates variable use as opposed to variable definition
					useArgs.add(StringConstant.v(vname));
					// if (vu.getValue() instanceof StaticInvokeExpr || vu.getValue() instanceof SpecialInvokeExpr) {
					if (vu.getValue() instanceof InvokeExpr) {
						// we won't need capture this type of value
						useArgs.add(g_null);
					}
					else {
						if (opts.notracingusedval() || opts.useblacktypes().contains(vu.getValue().getType().toString())) {
							useArgs.add(g_null);
						}
						else {
							if (vu.isStrConstObj()) {
								useArgs.add( vu.getValue() );
							}
							else if (vu.getValue() instanceof NewExpr) {
								// the lhs of a 'NewExpr' cannot be accessed before its 'specialInvoke' on the object's initializer is called : accessing it will cause
								// 'expect object/array on stack' VerifyErrors at runtime
								useArgs.add(g_null); 
							}
							else {
								useArgs.add( com.Utils.makeBoxedValue(m, vu.getValue(), useProbes) );
							}
							//useArgs.add( com.Utils.makeBoxedValue(m, vu.getValue(), useProbes) );
						}
					}
					//useArgs.add(IntConstant.v(System.identityHashCode(vu.getValue())));
					useArgs.add(g_null); // placeholder for base object
					//useArgs.add(StringConstant.v("")); // placeholder for array element index
					useArgs.add(g_null); // placeholder for array element index
					Stmt useCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr(mStmtStateReporter.makeRef(), useArgs ));
					if (dua.util.Util.isCtorCall(s) && !isActualParameter(vu.getValue(), n, m)) {
						// for safety, the used object from which a ctor is called should be monitored after the ctor is called, so be treated as a 'def'
						defProbes.add(0,useCall);
					}
					else {
						useProbes.add(useCall);
					}
					//insertProbe(pchn, useProbes, s, vu.getValue());
					continue;
				}
				/*
				if (vu.isConstant()) {
					// no need to trace this type of variables
					continue;
				}
				*/
				
				assert false; // should never get here
			}
			
			/** use of actual parameter and returned value are treated as definition (for formal parameter and the use of the returned
			 *	value, respectively.  
			 */
			/** solution: instead of marking them specially, do the use-def matching specially during post-processing */
			/*
			ReachableUsesDefs rudce = (ReachableUsesDefs) cfgdu;
			CallSite cs = n.getCallSite();
			if (cs != null) {
				Variable tgtVar = null;
				int startArgIdx = 0;
				if (cs.isInstanceCall()) {	startArgIdx = 1; }
				for(int i=startArgIdx; i<cs.getNumActualParams(); i++) {
					Value aval = cs.getActualParam(i);
				}
			}
			else if (s instanceof ReturnStmt && !s.getUseBoxes().isEmpty()) {
			}
			*/
			
			// insert the 'statement coverage' probes before the last 'statement state' probe above
			// insertProbe(pchn, stmtCovProbes, s, null);
			List<Object> allProbes = new ArrayList<Object>();
			allProbes.addAll(stmtCovProbes);
			/** use probes should be executed before definition probes, which is consistent with def-use semantics: after all, the def-vars are defined after use-vars are used first */
			allProbes.addAll(useProbes);
			/** for statement having in-place updates (writes), the use probes will have to be moved prior to the statement; in addition, to abide by the trace
			 * structure protocol, statement coverage probe should always be placed before any statement-state probes for the same statement 
			 */
			//if (!hasInPlaceUpdate(s) && n.getCallSite()==null) {
			if (!shouldSplitProbes(n)) {
				allProbes.addAll(defProbes);
			}
			
			Value tgtVal = null;
			if (!m.getActiveBody().getLocals().isEmpty()) {
				for (Variable v:defs) { 
					if (v.getValue() == m.getActiveBody().getLocals().getFirst()) { 
						tgtVal = v.getValue(); 
						break; 
					}
				}
				if (null == tgtVal) {
					for (Variable v:uses) {
						if (v.getValue() == m.getActiveBody().getLocals().getFirst()) { 
							tgtVal = v.getValue(); 
							break; 
						}
					}
				}
			}
			
			/*if (hasInPlaceUpdate(s) || n.getCallSite()!=null) */
			//InstrumManager.v().insertBeforeRedirect(pchn, stmtCovProbes, Utils.getFirstSafeNonIdStmtFrom(tgtVal, m, s, insertedStmtCache));
			if (shouldSplitProbes(n)) {
				InstrumManager.v().insertBeforeRedirect(pchn, allProbes, s);
				insertProbe(pchn, defProbes, s, tgtVal);
			}
			else {
				insertProbe(pchn, allProbes, s, tgtVal);
			}
		}
		return 0;
	}
	
	/** determine if we need split use probes and def probes around the monitored statement: for all call sites, we do this and 
	 *  for ctor calls, we use special treatments - treating the object from which the ctor is invoked as 'defined' instead of 'used'  
	 */
	public static boolean shouldSplitProbes(CFGNode n) {
		if (hasInPlaceUpdate(n.getStmt())) return true;
		if (n.getCallSite()==null) return false;
		/*
		for (SootMethod m: n.getCallSite().getAllCallees()) {
			if (m.getName().equals("<init>")) return false;
		}
		*/
		return true;
	}
	
	/** helper function for the statement-level event instrumenter -- determine if the given statement has in-place update or not.
	 * A typeical example of such statements is "r1 = r1.next".
	 * Instead of comparing the lhs defined value with the base local of the rhs field reference, we broadly check if there is non-empty intersection of the def set and use set 
	 */
	public static boolean hasInPlaceUpdate(Stmt s) {
		if (!(s instanceof AssignStmt)) {
			return false; 
		}
		
		NodeDefUses n = (NodeDefUses)ProgramFlowGraph.inst().getNode(s);
		Set<Variable> ds = new HashSet<Variable>(n.getDefinedVars());
		Set<Variable> us = new HashSet<Variable>(n.getUsedVars());
		ds.retainAll(us);
		//if (ds.isEmpty()) { return false; }
		if (ds.size()!=1) { return false; }
		if ( ((AssignStmt)s).getLeftOp() != ds.iterator().next().getValue()) { return false; }
		
		return true;
	}
	
	/** helper functions used for guaranteeing that method events are always captured prior to the statement-level events with respect to a same statement */
	private static boolean isMethodEventProbe(Stmt s) {
		String ss = s.toString();
		return ss.contains("EventMonitor: void initialize()") || 
			ss.contains("EventMonitor: void enter(java.lang.String)") || 
			(ss.contains("EventMonitor: void returnInto(java.lang.String,java.lang.String)") && ss.contains(": returnInto after calling"))
			|| ss.contains("EventMonitor: void terminate(java.lang.String)");
	}
	private static Stmt firstStmtPassMethodEventProbe(PatchingChain<Unit> pchain, Stmt s) {
		/** cannot pass over GotoStmt and IfStmt because the control flow would be messed up */
		while (s!=null && !(s instanceof GotoStmt || s instanceof IfStmt) && isMethodEventProbe(s)) {
			s = (Stmt)pchain.getSuccOf(s);
		}
		return s;
	}
	/** since we go through the patching chain in order, we should guarantee that no probe for a statement be inserted before the probe for any succeeding statements */  
	/** !!!!! Unfortunately, later it turned out that we cannot do so since there may be jumps (if-stmt) coming next that will mangle the semantic if we always do so */
	private static Stmt passLastTarget(PatchingChain<Unit> pchain, Stmt curTgt, Stmt lastTgt) {
		/*
		if (lastTgt==null || lastTgt==curTgt) return curTgt;
		Stmt s = curTgt;
		while (s!=null && !pchain.follows(s, lastTgt)) {
			s = (Stmt)pchain.getSuccOf(s);
			if (s==lastTgt) break;
		}
		if (s!=null) return s;
		*/
		//return curTgt;
		if (pchain.follows(curTgt, lastTgt)) return curTgt;
		return lastTgt;
	}
	
	/** maintain a method-specific cache of inserted statements to help avoid the interference of those statement on the ongoing instrumentation when necessary */
	private static Set<Object> insertedStmtCache = new HashSet<Object>();
	private static PatchingChain<Unit> prevChain = null;
	private static Stmt preTgt = null; 
	private static int insertProbe(PatchingChain<Unit> pchain, List<Object> monitorProbes, Stmt tgtStmt, Value tgtVal) {
		if (prevChain != pchain) { insertedStmtCache.clear(); preTgt=null; prevChain = pchain; }
		insertedStmtCache.addAll(monitorProbes);
		
		// if tgt is at a ID stmt, jump to the first non-ID stmt to insert the probe
		if (tgtStmt instanceof IdentityStmt) {
			Stmt actualTgt = Utils.getFirstSafeNonIdStmtFrom(tgtVal, ProgramFlowGraph.inst().getContainingMethod(tgtStmt), tgtStmt, insertedStmtCache);
			preTgt = passLastTarget(pchain, firstStmtPassMethodEventProbe(pchain, actualTgt), preTgt);
			InstrumManager.v().insertBeforeRedirect(pchain, monitorProbes, preTgt);
			return 0;
		}
		// if node is at a return stmt, insert probe prior to the return
		if (tgtStmt instanceof ReturnStmt || tgtStmt instanceof ReturnVoidStmt || tgtStmt instanceof ThrowStmt) {
			preTgt = passLastTarget(pchain, firstStmtPassMethodEventProbe(pchain, tgtStmt), preTgt);
			InstrumManager.v().insertAtProbeBottom(pchain, monitorProbes, preTgt);
			return 0;
		}
		// if node is at a goto/if stmt, insert probe prior to the stmt to guarantee that the stateReporter is to be executed
		if (tgtStmt instanceof GotoStmt || tgtStmt instanceof IfStmt) {
			preTgt = tgtStmt; //passLastTarget(pchain, firstStmtPassMethodEventProbe(pchain, tgtStmt), preTgt);
			InstrumManager.v().insertBeforeRedirect(pchain, monitorProbes, preTgt);
			return 0;
		}
		
		/** for StmtCov probe, just add it immediately after the statement covered -- this will gum up the trace structure */
		/*
		if (null == tgtVal) {
			InstrumManager.v().insertAfter(pchain, monitorProbes, tgtStmt);
			return 0;
		}
		*/
		
		// for other cases,  insert the probe immediately after the hosting statement (unless a new statement when we need jump after
		// the initialization of the instantiated object is done)
		/** inserting probe, which takes the object instance as parameter, for an object-new (excluding newArray) statement caused 
		 * too many troubles while doing so is actually unnecessary!
		 * Now that we do NOT pass the object instance to the probe for such new statements, we do not need to specially pass 
		 * over its specialinvoke to insert that probe anymore --- instead, just treat it as a normal assignment statement 
		 */
		Stmt actualtgt = (Stmt) pchain.getSuccOf(tgtStmt); // Utils.getSuccAfterNextSpecialInvokeStmt(pchain, tgtStmt, insertedStmtCache);
		assert actualtgt!=null;
		
		/** in ctors, we need to jump further behind the specialInvoke of superclass ctor for 'this' object */
		//try {
		Stmt _possibleTgt = Utils.getFirstSafeNonIdStmtFrom(tgtVal, ProgramFlowGraph.inst().getContainingMethod(tgtStmt), tgtStmt, insertedStmtCache);
		if (_possibleTgt!=null && pchain.follows(_possibleTgt, actualtgt)) {
			actualtgt = _possibleTgt;
		}
		/*
		} catch (Throwable t) {
			System.err.println("error occurred with stmt=" + tgtStmt + " in method " + ProgramFlowGraph.inst().getContainingMethod(tgtStmt));
			System.exit(-1);
		}*/
		
		/** special treatment for specialInvokeStmt that initializes a newly instantiated object */
		if (insertedStmtCache.contains(tgtStmt) || insertedStmtCache.contains(actualtgt)) {
			while (insertedStmtCache.contains(actualtgt)) {
				actualtgt = (Stmt) pchain.getSuccOf(actualtgt);
			}
			//insertedStmtCache.remove(tgtStmt);
		}
		
		preTgt = passLastTarget(pchain, firstStmtPassMethodEventProbe(pchain, actualtgt), preTgt);
		InstrumManager.v().insertBeforeNoRedirect(pchain, monitorProbes, preTgt);
		return 0;
	}
	private void insertCachedContentReporter() {
		for (SootMethod entryMethod : ProgramFlowGraph.inst().getEntryMethods()) {
			List<Object> probe = new ArrayList<Object>();
			
			Body entryBody = entryMethod.retrieveActiveBody();
			PatchingChain<Unit> pchainEntry = entryBody.getUnits();
			Stmt sEntryLast = (Stmt) pchainEntry.getLast();
			
			// Insert code to invoke report method
			Stmt reportCallStmt = Jimple.v().newInvokeStmt(
					Jimple.v().newStaticInvokeExpr(mCachedContentReporter.makeRef(), new ArrayList<Object>()));
			probe.add(reportCallStmt);
			
			InstrumManager.v().insertAtProbeBottom(pchainEntry, probe, sEntryLast);
		}
	}
	
} // -- public class EventInstrumenter  

/* vim :set ts=4 tw=4 tws=4 */

