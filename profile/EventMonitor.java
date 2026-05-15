/**
 * File: src/profile/EventMonitor.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      	Changes
 * -------------------------------------------------------------------------------------------
 * 01/15/14		hcai			created; all trace event monitors
 * 01/24/14		hcai			re-spun the design to make the monitors neat and complete
 * 02/06/14		hcai			added tracing object ids of heap object's bases, and indice of array elements
 * 03/05/14		hcai			move object id monitoring from static analysis phase, which is wrong, to runtime monitor
 * 03/06/14		hcai			fixed per-test trace segmentation 
 * 03/21/14		hcai			use separate timestamp for method and statement-state trace for easier matching within specified method/statement instance in post-process phase
 * 06/06/14		hcai			fixed array index tracing --- trace the value instead of the variable 
 * 06/10/14		hcai			fixed baseid tracing for non-reference type (which would cause wrong def-use matching for those types)
 * 06/15/14		hcai			supported statement state probe straddling (around call site specially) 
 * 06/18/14		hcai			debugged/tested, and now working, for XML-security after NanoXML and Schedule1:
 * 								- get rid of segmented traceCache content dumping which could break the context of dependence search in post-processing, 
 * 									or the monitor needs record some information to connect one segment to others and post-processing will incur
 * 									overhead --- each query handles multiple segments looking across all segments   
 * 07/17/14		hcai			(partially) handled reflection calls
 * 07/21/14		hcai			use default trace output files to accommodate running without using the TraceRunner 
 * 07/26/14		hcai			always track calling context even with no-caching mode, for easing debugging
 * 08/07/14		hcai			fixed the bug that disabling the 'value-tracing' option causes failure in tracing base object ids
 * 08/16/14		hcai			added option for profiling statement execution cost only
*/
package profile;

import java.io.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Stack;
import java.util.TreeMap;
import java.util.Map;
import java.util.zip.GZIPOutputStream;

import com.VariableInfo;

/** Monitoring method events in runtime upon invocations by probes instrumented in the subject.
 *  The baseline is method entry/exit events; more monitors like those for def-use/value monitoring can be added here as 'public static' members.
 *  In particular,
 *  - those statement-level events will be captured between the entry and exit event per method;
 *  - variable def-use and variable value events will be nested between two statement coverage events 
 */
public class EventMonitor {
	/*
	// memory cache of statement state with respect to its def-use variable ids, at the statement instance level : stmt id -> [[var ids] of each instance of the stmt])
	private static final Map<Integer, List<List<Integer>>> defuseCacheIns = new LinkedHashMap<Integer, List<List<Integer>>>();
	*/
	
	// the central cache of program state recording the all sorts of events as needed for a complete trace:
	// {<method id> -> {<timestamp as method instance number> -> { <stmt id> -> {<timestamp as statement instance number> -> [var ids] }}}}
	/*
	{<method id,timestamp> -> { <stmt id, timestamp> -> [var ids] }}
	private static final Map< Pair<Integer,Integer>, Map< Pair<Integer,Integer>, List<Integer>>> traceCache = 
		new LinkedHashMap< Pair<Integer,Integer>, Map< Pair<Integer,Integer>, List<Integer>>>();
	*/
	private static final Map< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>> traceCache = 
		new LinkedHashMap< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>>();
	
	private static int curMethod = 0;//, preMethod = -1;
	private static Stack<Integer> mstack = new Stack<Integer>();
	// now that statement state monitors for a call site can be split around the statement and the returnInto probe, we need this another stack
	// to maintain the 'current' statement
	//private static Stack<Integer> sstack = new Stack<Integer>();
	
	private static int curStmt = 0, preStmt = -1;
	
	/** the name of the file to save the dumped cache content */
	protected static String fnCachedStates = "/tmp/trace.ems";//"";
	/** if caching the states until the end of execution, or dumping in an immediate manner at each monitoring point */
	public static boolean cachingStates = true;
	
	/** if profiling statement-level execution costs : when this is enabled, only statementCov monitor is active and all other monitors disabled */
	public static boolean stmtExecTimeProfiling = false;
	public static String fnStmtProf = "/tmp/stmprof.emp";
	public static Map<Integer, List<Long> > stmtProfCache = new LinkedHashMap<Integer, List<Long>>(); // stmt id -> list of instance execution time
	
	/* the global time stamp for marking instance no. for statement-level events */
	protected static Integer g_ts = 0;
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// 1. Method Events
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	protected static final long CN_LIMIT = 1*10*1000; //5000000;
	/** counter of trace segments per test case trace */
	protected static int g_traceCnt = 0;
	
	/* the full method list in which the full event map will index for retrieving the method signature */
	protected static HashMap<String, Integer> S = new LinkedHashMap<String, Integer>();
	protected static Integer g_index = 1;
	
	/* all method events */
	protected static HashMap<Integer, Integer> A = new LinkedHashMap<Integer, Integer>();
	
	/* two special method events */
	public static final int PROGRAM_START = Integer.MIN_VALUE;
	public static final int PROGRAM_END = Integer.MAX_VALUE;
	
	/* the global counter of method-level events */
	protected static Integer g_counter = 0;
	
	/* debug flag: e.g. for dumping event sequence to human-readable format for debugging purposes, etc. */
	protected static boolean debugOut = false;
	public static void turnDebugOut(boolean b) { debugOut = b; }

	/* a flag ensuring the initialization and termination are both executed exactly once and they are paired*/
	protected static boolean bInitialized = false;
	
	/* file where method events are to be dumped at execution termination */ 
	protected static String fnMethodEventMaps = "/tmp/trace.em";
	
	public static boolean segmentTrace = false;
	
	/* The name of serialization target file will be set by EARun via this setter */
	public static void setEventSerializeFile(String fname) {
		if (cachingStates) {
			fnMethodEventMaps = fname;
			fnCachedStates = fname+"s";
		}
		
		fnStmtProf = fname + "p";
		
		resetInternals();
	}
	
	/* for Soot to recognize the 'EventMonitor' class */
	public static void __link() { }
	
	/* clean up internal data structures: typically we need to do so after the execution of a test case */
	private synchronized static void resetInternals() {
		
		A.clear();
		
		synchronized (g_index) {
			g_index = 1;
		}
		
		synchronized (g_counter) {
			g_counter = 0;
		}
		
		g_traceCnt = 0;
		
		if (!cachingStates) {
			return;
		}
	}
	
	/* initialize internal data structures before the first method event occurs */		
	public synchronized static void initialize() throws Exception{
		
		S.clear();
		A.clear();
		traceCache.clear();
		mstack.clear();
		
		synchronized (g_index) {
			g_index = 1;
		}
		
		synchronized (g_counter) {
			g_counter = 1;
			A.put(g_counter, PROGRAM_START);
			g_counter++;
		}
		
		g_traceCnt = 0;
		bInitialized = true;
		g_ts = 0;
		
		if (!cachingStates) {
			System.out.println("[Program Started]");
			return;
		}
	}
	
	/* method entry event: upon the method given by 'methodname' is executed */
	public synchronized static void enter(String methodname){
		
		try {
			/** !!! with this design of trace structure and protocol, it is impossible to implement the cached trace segmenting */
			/*
			if (g_counter > CN_LIMIT*(g_traceCnt+1)) { // segmented cache content dumping
				serializeMethodEvents();
				
				if (cachingStates && segmentTrace) {
					dumpCachedStates();
					//g_counter = 1;
				}
				
				g_traceCnt ++;
			}
			*/
			
			synchronized (g_index) {
				if (!S.containsKey(methodname)) {
					S.put(methodname, g_index);
					g_index ++;
				}
			}
			synchronized (g_counter) {
				assert S.containsKey(methodname);
				int midx = S.get(methodname);
				
				//preMethod = curMethod;
				curMethod = midx;
				mstack.push(curMethod);
				
				//sstack.push(curStmt);
				
				A.put(g_counter, midx*-1);  // negative index for entry event
				
				/* 
				Pair<Integer, Integer> mt = new Pair<Integer, Integer>(midx, g_counter);
				Map< Pair<Integer,Integer>, List<Integer>> stmtState = traceCache.get(mt); 
				*/
				Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>> mAllIns = traceCache.get(curMethod);
				if (null == mAllIns) {
					mAllIns = new LinkedHashMap<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>();
					traceCache.put(midx, mAllIns);
				}
				Map< Integer, Map<Integer, List<VariableInfo>>> mIns = mAllIns.get(g_counter);
				if (null == mIns) {
					mIns = new LinkedHashMap< Integer, Map<Integer, List<VariableInfo>>>();
					mAllIns.put(g_counter, mIns);
				}				
				
				g_counter ++;
				/** to accommodate the special need of segmenting the statement-state trace, move the following to the beginning: 
				 *  as such, reliance on the previous trace cache maintenance event (context) is removed 
				 */
				/*
				if (g_counter > CN_LIMIT*(g_traceCnt+1)) { // segmented cache content dumping
					serializeMethodEvents();
					
					if (cachingStates && segmentTrace) {
						dumpCachedStates();
						//g_counter = 1;
					}
					
					g_traceCnt ++;
				}
				*/
			}
		} catch (Throwable t) {
			//System.err.println("curmethod= " + curMethod + " when entering into " + methodname);
			t.printStackTrace(System.err);
		}
		
		if (!cachingStates) {
			System.out.println("Entered " + methodname);
			return;
		}

	}

	/* method returned-into event: upon the method given by 'calleeName' is returned into the caller 'methodname';
	 * the callee can be either an actual method called or a trap (exception block) 
	 */
	public synchronized static void returnInto(String methodname, String calleeName){
		
		try {
			synchronized (g_counter) {
				assert S.containsKey(methodname);
				
				assert !mstack.empty(); // sanity check
				//preMethod = curMethod;
				// note that "return-into" event happens not only as a callee exits but also in a catch block and/or a finally block 
				curMethod = mstack.peek(); 
				
				int midx = S.get(methodname);
				// method entry-exit--pairing check
				if (midx == curMethod) {
					// case 1: control flow was trapped into a catch/finally block instead of exiting from a callee when the caller should at the stack top
				}
				else {
					// case 2: the most recent callee is now exiting into its caller in the current context
					// get back to the context of the most recent caller
					mstack.pop();
					curMethod = mstack.peek();
					
					//sstack.pop();
				
					Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>> mAllIns = traceCache.get(curMethod);
					assert (null != mAllIns && mAllIns.size()>=1);
					List<Integer> mkeyList = new ArrayList<Integer>(mAllIns.keySet());
					assert (mkeyList.size()>=1);
					Map< Integer, Map<Integer, List<VariableInfo>>> mIns = mAllIns.get( mkeyList.get(mkeyList.size()-1) );
					List<Integer> skeyList = new ArrayList<Integer>(mIns.keySet());
					
					if (skeyList.size()>=1) {
						// for cases in which the statement-state probes straddle around the call site and this returnedInto probe
						preStmt = curStmt;
						curStmt = skeyList.get(skeyList.size()-1);
					}
				}
				/* DEBUG
				else {
					System.err.println("BAD: curStmt=" + curStmt + " curMethod=" + curMethod + " mAllIns=" + mAllIns +
							" callername=" + methodname + "-" + midx + " calleename=" + calleeName);
					System.exit(-1);
				}
				*/				
				
				A.put(g_counter, midx*1);  // positive index for returned-into event
				
				g_counter ++;
				
				/** to accommodate the special need of segmenting the statement-state trace, splinter/slice trace only at the entrance event */
				/*
				if (g_counter > CN_LIMIT*(g_traceCnt+1)) {
					serializeMethodEvents();
					
					if (cachingStates && segmentTrace) {
						dumpCachedStates();
						//g_counter = 1;
					}
					
					g_traceCnt ++;
				}
				*/
			}
		} catch (Throwable t) {
			//System.err.println("curmethod= " + curMethod + " when returned into " + methodname + " from " + calleeName);
			t.printStackTrace(System.err);
		}
		
		if (!cachingStates) {
			System.out.println("Retured into " + methodname + " from " + calleeName);
			return;
		}

	}
	
	public static Object getMap() { return A.clone(); }
	
	/* 
	 * program termination event: when this event occurs, we dump the event sequence cached in memory to the given file 
	 */
	public synchronized static void terminate(String where) throws Exception {
		if (!cachingStates) {
			System.out.println("[Program Terminated]");
			return;
		}
		if (bInitialized) { 
			bInitialized = false;
		}
		else {
			return;
		}

		synchronized (g_counter) {
			A.put(g_counter, PROGRAM_END);
		}
		
		if (debugOut) {
			dumpMethodEvents();
		}
		
		serializeMethodEvents();
	}
	
	/* write the sequence of method events as readable texts, primarily for debugging purposes */
	protected synchronized static void dumpMethodEvents() {
		System.out.println("\n[ Method Index ]\n");
		System.out.println(S);
		System.out.println("\n[ Full Sequence of Method Entry and Returned-into Events]\n");
		TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( A );
		System.out.println(treeA);
	}
	/* write the sequence of method events in a compact binary form */
	protected synchronized static void serializeMethodEvents() {
		/* serialize for later deserialization in the post-processing phase */
		if ( !fnMethodEventMaps.isEmpty() ) {
			FileOutputStream fos;
			try {
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				fos = new FileOutputStream(fnMethodEventMaps+(g_traceCnt>0?g_traceCnt:""));
				GZIPOutputStream goos = new GZIPOutputStream(fos);
				ObjectOutputStream oos = new ObjectOutputStream(bos);
				
				// First we need the method index for indexing methods because the full sequence does not contain method signature
				oos.writeObject(S);
				oos.writeObject(A);
				oos.flush();
				oos.close();
				
				goos.write(bos.toByteArray());
				bos.flush();
				bos.close();
				
				goos.flush();
				goos.close();
				
				fos.flush();
				fos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				A.clear();
				//g_counter = 1;
				//g_traceCnt ++;
			}
		}
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// 2. Statement-level Events
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	/** Used to avoid infinite recursion */
	private static boolean active = false;
	/** used to customize output stream */
	public static PrintStream outStream = null;
	
	/** report statement coverage */
	public synchronized static void reportStmtCov(int sid) {
		if (active) {
			return;
		}
		
		active = true;
		if (outStream == null) {
			outStream = System.err;
		}
		try {
			/** a simple lazy trick to automatically recognize if 'stmtExecTimeProfiling' is enabled during the instrumentation phase */
			if (stmtExecTimeProfiling && false == bInitialized) {
				bInitialized = true;
				//stmtExecTimeProfiling = true;
				stmtProfCache.clear();
				clock = 0L;
			}
			
			if (stmtExecTimeProfiling) {
				Long elapse = System.nanoTime() - clock;
				if (-1 == preStmt) {
					preStmt = sid;
				}
				else {
					preStmt = curStmt;
					List<Long> ets = stmtProfCache.get(preStmt);
					if (ets == null) {
						ets = new ArrayList<Long>();
						stmtProfCache.put(preStmt, ets);
					}
					ets.add(elapse);
				}
				curStmt = sid;
				clock = System.nanoTime();
			}
			else {
				reportStmtCov_Impl(sid);
			}
		}
		catch (Throwable t) {
			t.printStackTrace(outStream);
		}
		finally {
			active = false;
		}
		synchronized (g_ts) {
			g_ts ++;
		}
	}
	
	public synchronized static void reportStmtCov_Impl(int sid) {
		// report that a statement is covered
		preStmt = curStmt;
		curStmt = sid;
		/*if (cachingStates)*/ {
			Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>> mAllIns = traceCache.get(curMethod);
			assert (null != mAllIns && mAllIns.size()>=1);
			List<Integer> keyList = new ArrayList<Integer>(mAllIns.keySet());
			Map< Integer, Map<Integer, List<VariableInfo>>> mIns = mAllIns.get( keyList.get(keyList.size()-1) ); // the last method instance of curMetod is the current instance of it
			assert (null != mIns);
			Map<Integer, List<VariableInfo>> sAllIns = mIns.get(curStmt); 
			if (null == sAllIns) {
				sAllIns = new LinkedHashMap< Integer, List<VariableInfo> >();
				mIns.put(curStmt, sAllIns);
			}
			List<VariableInfo> sIns = sAllIns.get(g_ts);
			if (null == sIns) {
				sIns = new ArrayList<VariableInfo>();
				sAllIns.put(g_ts, sIns);
			}
		}
		/*else*/ if (!cachingStates) {
			//outStream.println("s"+sid);
			System.out.println("s"+sid);
		}
	}
	
	/** report statement states, concerning its variable def/use and variable values */ 
	public synchronized static void reportStmtState(int vid, String vname, Object vobj, Object vbase/*int baseId*/, /*String*/Object aridx) {
		if (active) {
			return;
		}
		
		active = true;
		if (outStream == null) {
			outStream = System.err;
		}
		try {
			reportStmtState_Impl(vid, vname, vobj, vbase, aridx);
		}
		catch (Throwable t) {
			t.printStackTrace(outStream);
		}
		finally {
			active = false;
		}
	}
	public static Long clock = 0l;
	/** vid - variable id, the index of variable to the global variable list; 
	 *  vobj - variable as an object; 
	 *  vbase - base object (for fieldRef and arrayRef only)   
	 *  // DISCARDED: baseId - base object id; (for fieldRef and arrayRef only)
	 *  aridx - array element index 
	 */
	public synchronized static void reportStmtState_Impl(int vid, String vname, Object vobj, Object vbase/*int baseId*/, /*String*/Object aridx) {
		// remove most of the addresses in default toString() output
		String oStr="";
		if (vobj != null /*&& !vval.toString().equals("null")*/) {
			String hc =  "@" + Integer.toHexString(vobj.hashCode());
			oStr = vobj.toString().replaceAll(hc, "");
			oStr = oStr.replace('\n', '|');
		}
		
		/** the 'baseId' passed in is not a runtime thus invalid one */
		/*
		if (baseId != 0 && vobj != null) {
			baseId = System.identityHashCode(vobj);
		}
		*/
		int baseId = 0;
		if (vbase != null) {
			baseId = System.identityHashCode(vbase);
		}
		
		// report a variable def (positive integer of vid) or use (negative integer of vid), and, optionally, the value of the variable specified by vid
		/*if (cachingStates)*/ {
			Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>> mAllIns = traceCache.get(curMethod);
			assert (null != mAllIns && mAllIns.size()>=1);
			List<Integer> mkeyList = new ArrayList<Integer>(mAllIns.keySet());
			Map< Integer, Map<Integer, List<VariableInfo>>> mIns = mAllIns.get( mkeyList.get(mkeyList.size()-1) ); // the last method instance of curMetod is the current instance of it
			
			if (!(null != mIns && mIns.size()>=1 && mIns.containsKey(curStmt))) {
				System.err.println("mIns="+mIns+" curStmt=" + curStmt + "  curMethod=" + curMethod);
			}
			
			assert (null != mIns && mIns.size()>=1 && mIns.containsKey(curStmt));
			
			Map<Integer, List<VariableInfo>> sAllIns = mIns.get(curStmt); 
			assert (null != sAllIns && sAllIns.size()>=1);
			List<Integer> skeyList = new ArrayList<Integer>(sAllIns.keySet());
			List<VariableInfo> sIns = sAllIns.get(skeyList.get(skeyList.size()-1)); // the last statement instance of curStmt is the current instance of it
			assert (null != sIns);
			
			VariableInfo varinfo = new VariableInfo(vid, vname, oStr);
			if (0 != baseId) { varinfo.setBaseId(baseId); }
			/*if (aridx.length()>0) { varinfo.setAridx(aridx); }*/
			if (aridx != null) { varinfo.setAridx(aridx.toString()); }
			synchronized (clock) {
				varinfo.setTS(clock/*System.currentTimeMillis()*/);
				//clock++;
			}
			sIns.add(varinfo);
		}
		/*else*/if (!cachingStates) {
			//outStream.print("v"+vid);
			System.out.print("curMethod=" + curMethod + " curStmt=" + curStmt + " ||| ");
			System.out.print("v"+vid + " " + vname);
			if (oStr.length()>0) {
				System.out.print(" val=" + (vobj == null? null : oStr));
			}
			if (baseId != 0) {
				System.out.print(" baseid=" + baseId);
			}
			/*if (aridx.length()>0) {*/
			if (aridx != null && aridx.toString().length()>0) {
				System.out.print(" aridx=" + aridx.toString());
			}
			synchronized (clock) {
				System.out.print(" ts=" + clock);
				//clock++;
			}
			
			if (preStmt != curStmt) { // put all info pertaining to a statement instance on a single text line
				//outStream.println();
				System.out.println();
			}
		}
		synchronized (clock) {
			clock++;
		}
	}
	
	/** report statement states on reflection call site */ 
	public synchronized static void reportReflectionCallState(Object me, Object obj, Object[] args) {
		if (active) {
			return;
		}
		
		active = true;
		if (outStream == null) {
			outStream = System.err;
		}
		try {
			reportReflectionCallState_Impl(me, obj, args);
		}
		catch (Throwable t) {
			t.printStackTrace(outStream);
		}
		finally {
			active = false;
		}
	}
	
	/** me - the method called; obj - the object from which me is called; args - the list of arguments passed to the method being called */
	public synchronized static void reportReflectionCallState_Impl(Object me, Object obj, Object[] args) {
		// report parameter variable uses according to the 'args' array
		if (cachingStates) {
			Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>> mAllIns = traceCache.get(curMethod);
			assert (null != mAllIns && mAllIns.size()>=1);
			List<Integer> mkeyList = new ArrayList<Integer>(mAllIns.keySet());
			Map< Integer, Map<Integer, List<VariableInfo>>> mIns = mAllIns.get( mkeyList.get(mkeyList.size()-1) ); // the last method instance of curMetod is the current instance of it
			
			if (!(null != mIns && mIns.size()>=1 && mIns.containsKey(curStmt))) {
				System.err.println("mIns="+mIns+" curStmt=" + curStmt + "  curMethod=" + curMethod);
			}
			
			assert (null != mIns && mIns.size()>=1 && mIns.containsKey(curStmt));
			
			Map<Integer, List<VariableInfo>> sAllIns = mIns.get(curStmt); 
			assert (null != sAllIns && sAllIns.size()>=1);
			List<Integer> skeyList = new ArrayList<Integer>(sAllIns.keySet());
			List<VariableInfo> sIns = sAllIns.get(skeyList.get(skeyList.size()-1)); // the last statement instance of curStmt is the current instance of it
			assert (null != sIns);
			
			for (int j = 0; j < args.length; ++j) {
				int vid = 0; /** to do: how to retrieve the vid (or other means for continuous use-def tracking) for each of the argument in the 'args' array */
				VariableInfo varinfo = new VariableInfo(vid, ""+"&AP#" + (j+1) + "@"+me, args[j].toString());
				synchronized (clock) {
					varinfo.setTS(clock/*System.currentTimeMillis()*/);
					clock++;
				}
				sIns.add(varinfo);
			}
		}
		else {
			for (int j = 0; j < args.length; ++j) {
				//outStream.print("v"+vid);
				System.out.print("v"+0 + " " + "");
				System.out.print("parameter #" + (j+1) + " val=" + args[j] + " passed to " + me + "via reflection");
			
				synchronized (clock) {
					System.out.print(" ts=" + clock);
					clock++;
				}
			}
			
			if (preStmt != curStmt) { // put all info pertaining to a statement instance on a single text line
				//outStream.println();
				System.out.println();
			}
		}
	}
	
	public synchronized static void reportBranch(int brid, int brtgt) {
		if (active) {
			return;
		}
		
		active = true;
		if (outStream == null) {
			outStream = System.out;
		}
		try {
			reportBranch_Impl(brid, brtgt);
		}
		catch (Throwable t) {
			t.printStackTrace(outStream);
		}
		finally {
			active = false;
		}
		
	}
	public synchronized static void reportBranch_Impl(int brid, int brtgt) {
		// branch id and the id of the target statement of the branch
		if (cachingStates) {
		}
		else {
			//outStream.print("b"+brid+"-"+brtgt);
			System.out.print("b"+brid+"-"+brtgt);
		}
	}
	
	/** dump cached content on statement level execution time profiling */ 
	public synchronized static void dumpCachedStmtProf() {
		/* serialize for later deserialization in the post-processing phase */
		if ( stmtExecTimeProfiling ) {
			assert fnStmtProf.length()>0;
			FileOutputStream fos;
			try {
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				fos = new FileOutputStream(fnStmtProf);
				GZIPOutputStream goos = new GZIPOutputStream(fos);
				ObjectOutputStream oos = new ObjectOutputStream(bos);
				
				// First we need the method index for indexing methods because the full sequence does not contain method signature
				oos.writeObject(stmtProfCache);
				oos.flush();
				oos.close();
				
				goos.write(bos.toByteArray());
				bos.flush();
				bos.close();
				
				goos.flush();
				goos.close();
				
				fos.flush();
				fos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				bInitialized = false;
			}
		}
	}
	/** dump cached content on full trace of program states */ 
	public synchronized static void dumpCachedStates() {
		if ( stmtExecTimeProfiling ) {
			// profiling the last statement
			Long elapse = System.nanoTime() - clock;
			
			preStmt = curStmt;
			List<Long> ets = stmtProfCache.get(preStmt);
			if (ets == null) {
				ets = new ArrayList<Long>();
				stmtProfCache.put(preStmt, ets);
			}
			ets.add(elapse);

			dumpCachedStmtProf();
			return;
		}
		/* serialize for later deserialization in the post-processing phase */
		if ( !fnCachedStates.isEmpty() ) {
			FileOutputStream fos;
			try {
				ByteArrayOutputStream bos = new ByteArrayOutputStream();
				fos = new FileOutputStream(fnCachedStates+((g_traceCnt)>0?(g_traceCnt):""));
				GZIPOutputStream goos = new GZIPOutputStream(fos);
				ObjectOutputStream oos = new ObjectOutputStream(bos);
				
				// First we need the method index for indexing methods because the full sequence does not contain method signature
				oos.writeObject(S);
				//oos.writeObject(A);
				oos.writeObject(traceCache);
				oos.flush();
				oos.close();
				
				goos.write(bos.toByteArray());
				bos.flush();
				bos.close();
				
				goos.flush();
				goos.close();
				
				fos.flush();
				fos.close();
			}
			catch (Exception e) {
				e.printStackTrace();
			}
			finally {
				if (cachingStates) { 
					traceCache.clear();
				}
			}
		}
	}
	
	/** give the full method trace length */
	public synchronized static int getFullTraceLength() {
		synchronized (g_counter) {
			return g_counter;
		}
	}
}

/* vim :set ts=4 tw=4 tws=4 */
