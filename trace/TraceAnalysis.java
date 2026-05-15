/**
 * File: src/trace/TraceAnalysis.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/24/14		hcai		created; for dynamic dependence analysis based on traces
 * 03/07/14		hcai		added multi-segment trace support 
 * 05/12/14		hcai		added all basic trace queries (all method activations; last def; all uses of def; and last CD)
 * 05/13/14		hcai		tested/fixed queries for method activations and last definition
 * 05/28/14		hcai		tested/fixed the query for all uses of a def
 * 05/29/14		hcai		tested/fixed the query for last CD source
 * 05/30/14		hcai		debugged query of all CD targets thus done all basic queries
 * 06/05/14		hcai		added a few other query routines and backward slice function
 * 06/06/14		hcai		tested/debugged backward dynamic slice computation as a query supported by Tracer
 * 06/10/14		hcai		fixed backward dynamic slice to avoid missing the last lastDef statement which has no non-library variable use 
 * 06/11/14		hcai		avoid infinite recursion when tracking lastDef/lastCD in backward dynamic slicing 
 * 06/13/14		hcai		added missing return and parameter passing reduced DDs in backward slicing
 * 06/15/14		hcai		debugged/tested dynamic slicing: working for schedule1 and nanoxml at least 
 * 06/16/14		hcai		improved performance of getLastCDRelax; finalized def-use matching
 * 06/18/14		hcai		debugged/tested, and now working, for XML-security after NanoXML and Schedule1:
 * 							- handle failing interDD link pairing to respect the inaccuracy of static analysis (due to polymorphisms/dynamic binding)
 * 							- handle lastDef and lastCD happen to be at the same statement instance as the queried use or CD target
 * 							- added missing statements in backward slice when the criteria has no any uses: added itself and tracking along lastCD
 * 7/12/14		hcai		rewrite core queries in response to removing uses of static DD information
 * 7/13/14		hcai		working version without static DDs being used in post-processing
 * 7/15/14		hcai		eliminated method-name matching from parameter/retval passing induced interDD pairing: use method name matching as
 * 							a double-check instead (which also enables straightforward handling of method calls by reflection)  
 * 7/17/14		hcai		added support for reflection calls (since no method name is traced on such call site, method-name matching is left out during 
 * 							relevant interDD pairing - which may lead to spurious matching, when the two cases for failing method-name matching happened in non-reflection call situations!)
 * 07/26/14		hcai		continue tracking dependencies from all uses on a call site where there is an actual parameter use to which a formal parameter is linked, instead of just
 *							just tracking along that actual parameter use.  
 * 
*/
package trace;
import java.io.*;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import profile.StaticCDInfo;
//import profile.StaticDDInfo;

import com.VariableInfo;

public class TraceAnalysis{
	static int nExecutions = Integer.MAX_VALUE;
	public static boolean debugOut = false;
	
	static StaticCDInfo cdinfo = null;
	//static StaticDDInfo ddinfo = null;
	
	// global variable ids dumped at static analysis
	static Map<String, Integer> variable2Id = new LinkedHashMap<String, Integer>(); 
	
	public static void main(String args[]){
		if (args.length < 1) {
			System.err.println("Too few arguments: \n\t " +
					"TraceAnalysis traceDir [numberTraces] [debugFlag]\n\n");
			return;
		}
		
		String traceDir = args[0]; // tell the directory where execution traces can be accessed
		//String binDir = args[1]; // tell the directory where the accessory files dumped during the static analysis are located
		
		// read at most N execution traces if specified, otherwise exhaust all to be found
		if (args.length > 1) {
			nExecutions = Integer.parseInt(args[1]);
		}
		
		if (args.length > 2) {
			debugOut = args[2].equalsIgnoreCase("-debug");
		}
		
		if (debugOut) {
			System.out.println("Try to read [" + (-1==nExecutions?"All available":nExecutions) + "] traces in "	+ traceDir);
		}
		
		try {
			loadAllStaticInfo(traceDir);
			startParseTraces(traceDir);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void loadAllStaticInfo(String traceDir) {
		if (variable2Id.isEmpty()) {
			readVariableIds(traceDir + File.separator + "varIds.out");
		}
		if (null == cdinfo) {
			if (null == readStaticCDs(traceDir+File.separator+"staticCDInfo.dat")) {
				System.err.println("Warning: static CD info is missing; ignored.");
			}
		}
		/*
		if (null == ddinfo) {
			if (null ==	readStaticDDs(traceDir+File.separator+"staticDDInfo.dat")) {
				System.err.println("Fatal: cannot load static DD info; DD tracing will be incomplete, unable to proceed!");
				return;
			}
		}
		*/
	}
	
	/** read variable id mapping */
	public static void readVariableIds(String fnVarIds) {
		if (!new File(fnVarIds).exists()) return;
		BufferedReader br;
		variable2Id.clear();
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnVarIds)));
			String ts = br.readLine();
			while(ts != null){
				String[] segs = ts.split("\\s+",2);
				assert segs.length >=2;
				variable2Id.put(segs[1], Integer.parseInt(segs[0]));
				
				ts = br.readLine();
			}
			br.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/** read static CDs if available */
	public static StaticCDInfo readStaticCDs(String fnStaticCD) {
		if (cdinfo != null) {
			return cdinfo;
		}
		
		cdinfo = new StaticCDInfo();
		if (0 != cdinfo.DeserializeFromFile(fnStaticCD)) {
			return null;
		}
		return cdinfo;
	}
	/** read static DDs */
	/*
	public static StaticDDInfo readStaticDDs(String fnStaticDD) {
		if (ddinfo != null) {
			return ddinfo;
		}
		
		ddinfo = new StaticDDInfo();
		if (0 != ddinfo.DeserializeFromFile(fnStaticDD)) {
			return null;
		}
		return ddinfo;
	}
	*/
	
	/** perform analysis with respect to a single execution trace */
	public static int parseSingleTrace(String traceDir, int tId) throws Exception {
		try {
			String fnTrace = traceDir  + File.separator + "test" + tId + ".em";
			if (debugOut) {
				System.out.println("\nProcessing execution trace for test no. " + tId);
			}
			
			// to handle multiple-file trace for a single test case
			int g_traceCnt = 0;
			while (true) {
				String curfnMethodTrace = fnTrace + (g_traceCnt>0?g_traceCnt:"");
				String curfnStateTrace = fnTrace + 's' + (g_traceCnt>0?g_traceCnt:"");
				if (!new File(curfnMethodTrace).exists()) {
					// all segments have been processed
					break;
				}
				assert new File(curfnStateTrace).exists(); // method trace and state trace should always be matched with the segment no.
				if (debugOut & g_traceCnt>0) {
					System.out.println("\n\tnow with trace segment no. " + g_traceCnt);	
				}
				
				g_traceCnt ++;
				
				TraceReader treader = new TraceReader();
				treader.setMethodTrace(curfnMethodTrace);
				treader.setStateTrace(curfnStateTrace);
				
				// read both method- and state-trace for this trace segment
				treader.readTrace(debugOut);
				
				/** quick test of the basic trace queries */
				System.out.println("\n ###### Testing result from input no. " + tId);
				testQueries(treader);
				
				if (debugOut) {
					//System.out.println(treader.getStructuredTrace());
				}
			}
		}
		catch (Exception e) {
			throw e;
		}
		return 0;
	}
	
	private static void testQueries(TraceReader treader) {
		// 1. test method activation querying
		System.out.println("=========== Method Activation Querying Test ==========");
		Set<List<Integer>> enexPnts = new LinkedHashSet<List<Integer>>();
		int meid = 2;
		System.out.println("All activations of method id=" + meid + ", name=" + treader.getIdx2Method().get(meid));
		if (0 != getMethodEntryExitPoints(treader, meid, enexPnts) || enexPnts.isEmpty()) {
			System.out.println("\t not found!");
		}
		else {
			for (List<Integer> enex : enexPnts) {
				System.out.println("\t enter at ts=" + enex.get(0) + " and exit at ts=" + enex.get(1));
			}
			System.out.println();
		}
		
		// 2. test getVariableDefUses and getLastDef
		System.out.println("=========== Last Definition Querying Test ==========");
		int sid = 102;
		List<VariableInfo> varinfos = getVariableDefUses(treader, sid, -1);
		for (VariableInfo varin : varinfos) {
			if (varin.getVarId() > 0) continue;
			System.out.println("last def of var " + varin + " at " + sid + "^1 : ");
			
			List<Integer> ldstmtins = new ArrayList<Integer>();
			VariableInfo varinfo = getLastDef(treader, sid, -1, Math.abs(varin.getVarId()), ldstmtins);
			if (null != varinfo) {
				System.out.println("\t" + varinfo + " at " + ldstmtins.get(0) + " ts=" + ldstmtins.get(1));
			}
			else {
				System.out.println("\t not found!");
			}
			System.out.println();
		}
		
		// 3. test getAllUsesOfDef
		System.out.println("=========== All Uses of Definition Querying Test ==========");
		sid = 105;
		varinfos = getVariableDefUses(treader, sid, -1);
		for (VariableInfo varin : varinfos) {
			if (varin.getVarId() < 0) continue;
			System.out.print("uses of the def of var " + varin + " at " + sid + "^1 : ");
			
			List< List<Integer> > ustmtins = new ArrayList<List<Integer>>();
			List<VariableInfo> allUseVarinfo = getAllUsesOfDef(treader, 105, -1, Math.abs(varin.getVarId()), ustmtins);
			if (allUseVarinfo.isEmpty()) {
				System.out.println("\t not found!");
				continue;
			}
			int i = 0;
			for (VariableInfo varinfo : allUseVarinfo) {
				System.out.print("\n\t" + varinfo + " at " + ustmtins.get(i).get(0) + " ts=" + ustmtins.get(i).get(1));
				i++;
			}
			System.out.println();
		}
		System.out.println();
		
		// 4. test getLastCD
		System.out.println("=========== Last CD Querying Test ==========");
		sid = 120;
		List<Integer> lastcdStmtIns = getLastCD(treader, sid, -1);
		System.out.println("last cd of " + sid + "^1: ");
		if (lastcdStmtIns==null || lastcdStmtIns.isEmpty()) {
			System.out.println("\t not found!");
		}
		else {
			System.out.println("\t statement " + lastcdStmtIns.get(0) + " ts=" + lastcdStmtIns.get(1));
		}
		System.out.println();
		
		// 5. test getAllCDTgts
		System.out.println("=========== All CD Targets Querying Test ==========");
		sid = 177;
		List<List<Integer>> cdtgtsInses = getAllCDTgts(treader, sid, -1);
		System.out.println("CD targets of " + sid + "^1: ");
		if (cdtgtsInses==null || cdtgtsInses.isEmpty()) {
			System.out.println("\t not found!");
		}
		else {
			for (List<Integer> cdtgtins : cdtgtsInses) {
				System.out.println("\t statement " + cdtgtins.get(0) + " ts=" + cdtgtins.get(1));
			}
		}
		System.out.println();
		
		// 6. test getBackwardSlice
		System.out.println("=========== Backward dynamic slice Test ==========");
		sid = 233;
		Set<Integer> slice = getBackwardSlice(treader, sid);
		System.out.println("backward slice of " + sid + ": ");
		if (slice.isEmpty()) {
			System.out.println("\t is empty!");
		}
		else {
			for (Integer s : slice) {
				System.out.println("\t  " + s);
			}
		}
		System.out.println();
	}
	
	public static void startParseTraces(String traceDir) {
		int tId;
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			try {
				if ( parseSingleTrace(traceDir, tId) < 0 ) {
					// ignore erroneous or problematic traces
					continue;
				}
				
				// -- DEBUG
				if (debugOut) {
					
				}
			}
			catch (FileNotFoundException e) { 
				break;
			}
			catch (IOException e) {
				throw new RuntimeException(e); 
			}
			catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		System.out.println(--tId + " execution traces have been processed.");
		printStatistics(true);
	}
	
	private static void printStatistics (boolean btitle) {
		if (btitle) {
			System.out.println("\n============ Trace Result ================");
		}
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////
	//////////////////////////// core queries to a trace /////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////////
	/**
	 * retrieve all entries and exits of the specified method
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param midx [in] the method id of the method for which this query is performed
	 * @param enexPnts [out] the time stamps of each pair of entry and exit events of the method 
	 * @return 0 for success and negative numbers as error codes otherwise
	 */
	public static int getMethodEntryExitPoints(TraceReader reader, int midx, Set<List<Integer>> enexPnts) 
	{
		if (reader==null || reader.isEmpty()) {
			// trace must be parsed successfully first
			return -1;
		}
		
		// map from time stamp to method id
		Map<Integer, Integer> time2midx = reader.getEMSequence();
		if (!time2midx.containsValue(midx)) {
			// the specified method is not exercised by the trace underlying the given trace reader object
			return -2;
		}
		//Map<Integer, Integer> midx2time = new LinkedHashMap<Integer, Integer>();
		// Integer pret = null; // time-stamp of the preceding event
		Map.Entry<Integer, Integer> preEvent = null; // the preceding event
		List<Integer> enexPair = new ArrayList<Integer>(2);
		for (Map.Entry<Integer, Integer> en : time2midx.entrySet()) {
			//midx2time.put(en.getValue(), en.getKey());
			if (Math.abs(en.getValue()) != midx) {
				//pret = en.getKey();
				if (en.getValue() > 0 && preEvent != null && Math.abs(preEvent.getValue()) == midx) {
					// the return event of the specified method
					assert enexPair.size()==1;
					enexPair.add(en.getKey());
					enexPnts.add(new ArrayList<Integer>(enexPair));
					enexPair.clear();
				}
				preEvent = en;
				continue;
			}
			
			// negative midx indicates method entry event
			if (en.getValue() < 0) {
				assert enexPair.isEmpty();
				enexPair.add(en.getKey());
				//pret = en.getKey();
				preEvent = en;
				continue;
			}
			
			// encountered a returned-into event of a method now, 
			// then the immediately previous event should be the entry event of that method
			// assert pret != null;
			/** here it is an event that a method returned into the specified method, which we don't care now */
			preEvent = en;
		}
		return 0;
	} // getMethodEntryExitPoints
	
	/** helper function: retrieve variable def/use at the given statement occurrence according to the given set of identifiers */
	protected static List<VariableInfo> getVariableDefUses(TraceReader reader, int stmtid, int ins)
	{
		List<VariableInfo> retvinfo = new ArrayList<VariableInfo>();
		if (reader==null || reader.isEmpty()) {
			// trace must be parsed successfully first
			return retvinfo;
		}
		/** straightforward search in accordance with the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// search all instances of each method
				for (Integer sid : reader.getStructuredTrace().get(mid).get(mins).keySet()) {
					// search all statements in each method instance
					if (stmtid != sid) {
						// match target statement
						continue;
					}

					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						// search all instances of each statement
						if (-1!=ins && stmtins != ins) {
							// match target statement instance
							continue;
						}

						retvinfo.addAll(reader.getStructuredTrace().get(mid).get(mins).get(sid).get(stmtins));
					} // for each statement instance
					if (!retvinfo.isEmpty()) break;
				} // for each statement
			} // for each method instance
		} // for each method
		return retvinfo;
	}
	
	/**
	 * locate the definition of the variable specified by the given vid and retrieve the complete variable def info
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param vid [in] the variable id of the use queried
	 * @return the variable def being asked for
	 */
	public static VariableInfo getVariableDef(TraceReader reader, int stmtid, int ins, int vid)
	{
		List<VariableInfo> retvinfo = getVariableDefUses(reader, stmtid, ins);
		
		for (VariableInfo vinfo : retvinfo) {
			// search all variable defs/uses at this statement instance
			if (Math.abs(vinfo.getVarId())!=Math.abs(vid)) {
				// match variable by id
				continue;
			}
			if (vinfo.getVarId() < 0) {
				// match variable def/use
				continue;
			}
			
			return vinfo;
		} // for each variable use/def
		
		return null;
	}
	
	/**
	 * locate the use of the variable specified by the given vid and retrieve the complete variable use info
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param vid [in] the variable id of the use queried
	 * @return the variable use being asked for
	 */
	public static VariableInfo getVariableUse(TraceReader reader, int stmtid, int ins, int vid)
	{
		List<VariableInfo> retvinfo = getVariableDefUses(reader, stmtid, ins);
		
		for (VariableInfo vinfo : retvinfo) {
			// search all variable defs/uses at this statement instance
			if (Math.abs(vinfo.getVarId())!=Math.abs(vid)) {
				// match variable by id
				continue;
			}
			if (vinfo.getVarId() > 0) {
				// match variable def/use
				continue;
			}
			
			return vinfo;
		} // for each variable use/def
		
		return null;
	}
	
	/**
	 * helper function: retrieve all instances---their time stamps---of the given statement from the trace specified
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @return the list of all instances' time-stamp
	 */
	public static List<Integer> getAllStmtInstances(TraceReader reader, int stmtid)
	{
		List<Integer> allstmtIns = new ArrayList<Integer>();
		if (reader==null || reader.isEmpty()) {
			// trace must be parsed successfully first
			return allstmtIns;
		}
		/** straightforward search in accordance with the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// check execution of the specified statement in current method instance
				if (reader.getStructuredTrace().get(mid).get(mins).keySet().contains(stmtid)) {
					// collect all instances of the target statement
					allstmtIns.addAll( reader.getStructuredTrace().get(mid).get(mins).get(stmtid).keySet() );
				}
			} // for each method instance
			if (!allstmtIns.isEmpty()) {
				// a statement can execute in one method only
				break;	
			}
		} // for each method
		
		return allstmtIns;
	}
	
	/**
	 * retrieve all method instances---their time stamps---that executed the given statement in the trace specified
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param methodins [out] the list of all method instances' time-stamp 
	 * @return the enclosing method's id
	 */
	public static int getAllMethodInstancesOfStmt(TraceReader reader, int stmtid, List<Integer> meIns)
	{
		int target_mid = -1;
		if (reader==null || reader.isEmpty()) {
			// trace must be parsed successfully first
			return target_mid;
		}
		
		/** straightforward search in accordance with the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// check execution of the given statement in this method instance
				if (reader.getStructuredTrace().get(mid).get(mins).keySet().contains(stmtid)) {
					target_mid = mid;
					meIns.add(mins);
				}
			} // for each method instance
			if (-1 != target_mid) {
				// a statement can execute in one method only
				break;
			}
		} // for each method
		
		return target_mid;
	}
	
	public static List<VariableInfo> getAllUsesAtStmt(TraceReader reader, int stmtid) 
	{
		List<VariableInfo> retvinfo = getVariableDefUses(reader, stmtid, -1);
		List<VariableInfo> _retinfo = new ArrayList<VariableInfo>();
		for (VariableInfo vinfo : retvinfo) {
			// search all variable defs/uses at this statement instance
			if (vinfo.getVarId() < 0) {
				_retinfo.add(vinfo);
			}
		} // for each variable use/def
		
		return _retinfo;
	}
	public static List<VariableInfo> getAllDefsAtStmt(TraceReader reader, int stmtid) 
	{
		List<VariableInfo> retvinfo = getVariableDefUses(reader, stmtid, -1);
		List<VariableInfo> _retinfo = new ArrayList<VariableInfo>();
		for (VariableInfo vinfo : retvinfo) {
			// search all variable defs/uses at this statement instance
			if (vinfo.getVarId() > 0) {
				_retinfo.add(vinfo);
			}
		} // for each variable use/def
		
		return _retinfo;
	}
	
	/**
	 * retrieve the location information of the specified variable record (VariableInfo)
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param vinfo [in] the variable record
	 * @param varloc [out] the array of {statement id, statement ins, method id, method ins} 
	 * @return 0 for successful search and -1 otherwise
	 */
	public static int getVariableLocation(TraceReader reader, VariableInfo vinfo, List<Integer> varloc) {
		/** straightforward search in accordance with the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// search all instances of each method
				for (Integer sid : reader.getStructuredTrace().get(mid).get(mins).keySet()) {
					// search all statements in each method instance
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						// search all instances of each statement
						for (VariableInfo _v : reader.getStructuredTrace().get(mid).get(mins).get(sid).get(stmtins)) {
							// search all variable defs/uses at this statement instance
							if (vinfo.equals(_v)) {
								varloc.add(0, sid);
								varloc.add(1, stmtins);
								varloc.add(2, mid);
								varloc.add(3, mins);
								return 0;
							}
						} // for each variable use/def
					} // for each statement instance
				} // for each statement
			} // for each method instance
		} // for each method
		return -1;
	}
	
	/**
	 * retrieve the last definition of the specified variable use at the given particular statement instance
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param vid [in] the variable id of the use queried
	 * @param ldstmtins [out] the statement id and instance number of the last definition asked for 
	 * @return the variable indicating the last definition asked for
	 */
	public static VariableInfo getLastDef(TraceReader reader, int stmtid, int ins, int vid, List<Integer> ldstmtins)
	{
		VariableInfo retvinfo = null;
		VariableInfo tgtUse = getVariableUse(reader, stmtid, ins, vid);
		if (tgtUse==null) {
			// use not found; won't be able to find its def
			return retvinfo;
		}
		
		/** quickly locate the last Def in the variable view */
		ListIterator<VariableInfo> iter = reader.getVariableView().listIterator(reader.getVariableView().size());
		while (iter.hasPrevious()) {
			VariableInfo curv = iter.previous();
			if (curv.getTS() > tgtUse.getTS() || curv.getVarId()<0) {
				continue;
			}
			// DEBUG if (curv.getVarId() == Math.abs(tgtUse.getVarId())) { System.out.println("got ."); }
			if (curv.dupair(tgtUse)) {
				retvinfo = curv;
				// the first defined variable with smaller time-stamp and with matched variable info is the last def
				break;
			}
		}
		
		if (null != retvinfo) {
			assert 0 == getVariableLocation(reader, retvinfo, ldstmtins);
		}
				
		return retvinfo;
	} // getLastDef
	/** alternative version of getLastDef: does not rely on the trace structure protocol that constrains the items in each level of maps
	 *  are (ascendingly) ordered by their first-occurrence time, and no statement instance in method A is larger than any statement instances
	 *  in methods after A   
	 */
	public static VariableInfo getLastDefRelax(TraceReader reader, int stmtid, int ins, int vid, List<Integer> ldstmtins)
	{
		VariableInfo retvinfo = null;
		VariableInfo tgtUse = getVariableUse(reader, stmtid, ins, vid);
		if (tgtUse==null) {
			// use not found; won't be able to find its def
			return retvinfo;
		}
		
		int retsid = -1, retins = -1; // flags marking if the objective query results have been solved
		VariableInfo retfinal = null;
		int largestins = -1;
		
		/** straightforward search in accordance with the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// search all instances of each method
				for (Integer sid : reader.getStructuredTrace().get(mid).get(mins).keySet()) {
					// search all statements in each method instance
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						// search all instances of each statement
						for (VariableInfo vinfo : reader.getStructuredTrace().get(mid).get(mins).get(sid).get(stmtins)) {
							// search all variable defs/uses at this statement instance
							/*
							if (Math.abs(vinfo.getVarId())!=vid) {
								// match variable by id
								continue;
							}
							*/
							if (vinfo.getVarId() > 0 && vinfo.dupair(tgtUse)) {
								// match variable def/use
								retvinfo = vinfo; // save the last definition of the target variable
								retsid = sid;
								retins = stmtins;
							}

							if (retvinfo == null || (-1!=ins && retins > ins)) {
								continue;
							}
							// target variable use found, now retvinfo already has the its last definition
							assert retvinfo != null; // now at least one definition must occur before the queried use
							assert retsid != -1;
							assert retins != -1 && (-1==ins || retins <= ins);
							if (-1==largestins) {
								if (ldstmtins != null) {
									ldstmtins.add(0, retsid);
									ldstmtins.add(1, retins);
								}
								largestins = retins;
								retfinal = retvinfo;
							}
							else {
								// always take the target of largest instance number, which implies the *last*
								if (retins > largestins) {
									if (ldstmtins != null) {
										ldstmtins.set(0, retsid);
										ldstmtins.set(1, retins);
									}
									largestins = retins;
									retfinal = retvinfo;
								}
							}
						} // for each variable use/def
					} // for each statement instance
				} // for each statement
			} // for each method instance
		} // for each method
		if (retfinal == null) {
			// definition of library objects, such as System.out, is not traced
			if (debugOut) {
				System.out.println("Warning: last def of " + tgtUse + " NOT found.");
			}
		}
		return retfinal;
	} // getLastDefRelax
	
	/**
	 * retrieve all uses of the specified definition in terms of the statement, its instance id and variable id (some statements have
	 * multiple defined variables such as library objects
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param vid [in] the variable id of the definition being queried
	 * @param ustmtins [out] the statement ids and instance numbers of the uses asked for 
	 * @return the list of variables indicating the uses asked for
	 */
	public static List<VariableInfo> getAllUsesOfDef(TraceReader reader, int stmtid, int ins, int vid, List< List<Integer> > ustmtins)
	{
		List<VariableInfo> retvinfo = new ArrayList<VariableInfo>();
		VariableInfo tgtDef = getVariableDef(reader, stmtid, ins, vid);
		if (null == tgtDef) {
			// failed to locate the designated variable def, cannot proceed
			return retvinfo;
		}
		
		/* collect all uses of the target def via the variable view */
		ListIterator<VariableInfo> iter = reader.getVariableView().listIterator();
		while (iter.hasNext()) {
			VariableInfo curv = iter.next();
			if (curv.getTS() < tgtDef.getTS() || curv.getVarId()>0) {
				continue;
			}
			if (curv.dupair(tgtDef)) {
				List<Integer> curins = new ArrayList<Integer>();
				assert 0 == getVariableLocation(reader, curv, curins);
				
				retvinfo.add(curv);
				ustmtins.add(curins);
			}
		}
		
		return retvinfo;
	} // getAllUsesOfDef
	/** alternative version of getAllUsesOfDef: does not rely on the trace structure protocol that constrains the items in each level of maps
	 *  are (ascendingly) ordered by their first-occurrence time, and no statement instance in method A is larger than any statement instances
	 *  in methods after A   
	 */
	public static List<VariableInfo> getAllUsesOfDefRelax(TraceReader reader, int stmtid, int ins, int vid, List< List<Integer> > ustmtins)
	{
		List<VariableInfo> retvinfo = new ArrayList<VariableInfo>();
		if (reader==null || reader.isEmpty()) {
			// trace must be parsed successfully first
			return retvinfo;
		}
		VariableInfo targetVinfo = getVariableDef(reader, stmtid, ins, vid); // complete info of the target variable
		if (null == targetVinfo) {
			return retvinfo;
		}
		
		/** straightforward search according to the trace structure */
		for (Integer mid : reader.getStructuredTrace().keySet()) {
			// search all methods
			for (Integer mins : reader.getStructuredTrace().get(mid).keySet()) {
				// search all instances of each method
				for (Integer sid : reader.getStructuredTrace().get(mid).get(mins).keySet()) {
					// search all statements in each method instance
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						// search all instances of each statement
						for (VariableInfo vinfo : reader.getStructuredTrace().get(mid).get(mins).get(sid).get(stmtins)) {
							// search all variable defs/uses at this statement instance
							if (vinfo.getVarId() < 0) {
								// match variable use
								if (targetVinfo !=null && targetVinfo.dupair(vinfo) && (-1==ins || stmtins >= ins)) {
									retvinfo.add(vinfo); // save the use of the target variable after the definition
								
									if (ustmtins != null) {
										List<Integer> curins = new ArrayList<Integer>(2);
										curins.add(0, sid);
										curins.add(1, stmtins);
										ustmtins.add(curins);
									}
								}
							} // on encounter of uses of the target variable
						} // for each variable use/def
					} // for each statement instance
				} // for each statement
			} // for each method instance
		} // for each method
		
		return retvinfo;
	} // getAllUsesOfDefRelax
	
	/**
	 * retrieve the last CD (source) of the given statement occurrence
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @return the statement occurrence on which the specified statement is control dependent
	 */
	public static List<Integer> getLastCD(TraceReader reader, int stmtid, int ins)
	{
		if (cdinfo == null || reader==null || reader.isEmpty()) {
			// static CD info is required; trace must be parsed successfully first
			return null;
		}
		List<Integer> allSrcs = cdinfo.getCDSrcs(stmtid);
		if (allSrcs == null || allSrcs.isEmpty()) {
			// no valid static CD info; bail out now
			return null;
		}
		
		boolean bsid = false, bins = false; // flags marking if the target statement instance has been reached
		List<Integer> cdstmtins = new ArrayList<Integer>(2);  
		
		/** backward search in the structured trace */
		List<Integer> mids = new ArrayList<Integer>(reader.getStructuredTrace().keySet());
		for (int i=mids.size()-1; i>=0; i--) {
			Integer mid = mids.get(i);
			// search all methods
			List<Integer> minses = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).keySet());
			for (int j=minses.size()-1; j>=0; j--) {
				Integer mins = minses.get(j);
				// search all instances of each method
				List<Integer> sids = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).get(mins).keySet());
				for (int k=sids.size()-1; k>=0; k--) {
					// search all statements in each method instance
					Integer sid = sids.get(k);
					if (!bsid) {
						// match target statement
						bsid = stmtid == sid;
						if (!bsid) continue;
						if (-1!=ins && !reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet().contains(ins)) return null;
						else bins = true;
					}
					
					assert bsid && bins;

					if (allSrcs.contains(sid)) {
						List<Integer> stmtinses = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet());
						// the latest occurrence of the CD source is the solution
						for (int r = stmtinses.size()-1; r>=0; r--) {
							Integer stmtins = stmtinses.get(r);
							if (-1==ins || stmtins < ins) {
								cdstmtins.add(0, sid);
								cdstmtins.add(1, stmtins);
								return cdstmtins;
							}
						}
					}
				} // for each statement in the method instance 
			} // for each instance of the method
		} // for each method 
		return cdstmtins;
	} // getLastCD
	/** alternative version of getLastCD: does not rely on the trace structure protocol that constrains the items in each level of maps
	 *  are (ascendingly) ordered by their first-occurrence time, and no statement instance in method A is larger than any statement instances
	 *  in methods after A
	 */
	public static List<Integer> getLastCDRelax(TraceReader reader, int stmtid, int ins)
	{
		if (cdinfo == null || reader==null || reader.isEmpty()) {
			// static CD info is required; trace must be parsed successfully first
			return null;
		}
		List<Integer> allSrcs = cdinfo.getCDSrcs(stmtid);
		if (allSrcs == null || allSrcs.isEmpty()) {
			// no valid static CD info; bail out now
			return null;
		}
		
		List<Integer> cdstmtins = new ArrayList<Integer>(2);  
		
		/** backward search in the structured trace */
		List<Integer> mids = new ArrayList<Integer>(reader.getStructuredTrace().keySet());
		for (int i=mids.size()-1; i>=0; i--) {
			Integer mid = mids.get(i);
			// search all methods
			List<Integer> minses = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).keySet());
			for (int j=minses.size()-1; j>=0; j--) {
				Integer mins = minses.get(j);
				// search all instances of each method
				List<Integer> sids = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).get(mins).keySet());
				for (int k=sids.size()-1; k>=0; k--) {
					// search all statements in each method instance
					Integer sid = sids.get(k);
					if (!allSrcs.contains(sid)) {
						continue;
					}
					int largestins = Integer.MIN_VALUE;
					int smallestins = Integer.MAX_VALUE;
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						if (stmtins > largestins && (-1==ins || stmtins <= ins)) largestins = stmtins;
						if (stmtins < smallestins) smallestins = stmtins;
					}
					if (-1!=ins && smallestins > ins) {
						continue;
					}
					
					if (cdstmtins.isEmpty()) {
						cdstmtins.add(0, sid);
						cdstmtins.add(1, largestins);
					}
					else {
						if (largestins > cdstmtins.get(1)) {
							cdstmtins.set(0, sid);
							cdstmtins.set(1, largestins);
						}
					}
				} // for each statement in the method instance 
			} // for each instance of the method
		} // for each method 
		return cdstmtins;
	} // getLastCDRelax
	 
	/**
	 * retrieve all CD targets of the given statement occurrence
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @return the statements (with their occurrences) that are control dependent on the given statement instance
	 */
	public static List<List<Integer>> getAllCDTgts(TraceReader reader, int stmtid, int ins)
	{
		if (cdinfo == null || reader==null || reader.isEmpty()) {
			// static CD info is required; trace must be parsed successfully first
			return null;
		}
		List<Integer> allTgts = cdinfo.getCDTgts(stmtid);
		if (allTgts == null || allTgts.isEmpty()) {
			// no valid static CD info; bail out now
			return null;
		}
		
		boolean bsid = false, bins = false; // flags marking if the target statement instance has been reached
		List<List<Integer>> cdstmtins = new ArrayList<List<Integer>>();  
		
		/** forward search in the structured trace */
		List<Integer> mids = new ArrayList<Integer>(reader.getStructuredTrace().keySet());
		for (int i=0; i<mids.size(); i++) {
			Integer mid = mids.get(i);
			// search all methods
			List<Integer> minses = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).keySet());
			for (int j=0; j<minses.size(); j++) {
				Integer mins = minses.get(j);
				// search all instances of each method
				List<Integer> sids = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).get(mins).keySet());
				for (int k=0; k<sids.size(); k++) {
					Integer sid = sids.get(k);
					if (!bsid) {
						// match target statement
						bsid = stmtid == sid;
						if (!bsid) continue;
					}

					// search all statements in each method instance
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						if (!bins) {
							// match target statement instance
							bins = -1==ins || stmtins == ins;
							if (!bins) continue;
						}
						
						if (allTgts.contains(sid)) {
							List<Integer> onetgtins = new ArrayList<Integer>(2);
							if (-1==ins || stmtins > ins) {
								onetgtins.add(0, sid);
								onetgtins.add(1, stmtins);
								cdstmtins.add(onetgtins);
							}
						}
					} // for each instance of the statement
				} // for each statement in the method instance
			} // for each instance of the method
		} // for each method
		return cdstmtins;
	} // getAllCDTgts
	/** alternative version of getAllCDTgts: does not rely on the trace structure protocol that constrains the items in each level of maps
	 *  are (ascendingly) ordered by their first-occurrence time, and no statement instance in method A is larger than any statement instances
	 *  in methods after A
	 */
	public static List<List<Integer>> getAllCDTgtsRelax(TraceReader reader, int stmtid, int ins)
	{
		if (cdinfo == null || reader==null || reader.isEmpty()) {
			// static CD info is required; trace must be parsed successfully first
			return null;
		}
		List<Integer> allTgts = cdinfo.getCDTgts(stmtid);
		if (allTgts == null || allTgts.isEmpty()) {
			// no valid static CD info; bail out now
			return null;
		}
		
		List<List<Integer>> cdstmtins = new ArrayList<List<Integer>>();  
		
		/** forward search in the structured trace */
		List<Integer> mids = new ArrayList<Integer>(reader.getStructuredTrace().keySet());
		for (int i=0; i<mids.size(); i++) {
			Integer mid = mids.get(i);
			// search all methods
			List<Integer> minses = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).keySet());
			for (int j=0; j<minses.size(); j++) {
				Integer mins = minses.get(j);
				// search all instances of each method
				List<Integer> sids = new ArrayList<Integer>(reader.getStructuredTrace().get(mid).get(mins).keySet());
				for (int k=0; k<sids.size(); k++) {
					Integer sid = sids.get(k);
					// search all statements in each method instance
					if (!allTgts.contains(sid)) {
						continue;
					}
					for (Integer stmtins : reader.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						List<Integer> onetgtins = new ArrayList<Integer>(2);
						if (-1==ins || stmtins > ins) {
							onetgtins.add(0, sid);
							onetgtins.add(1, stmtins);
							cdstmtins.add(onetgtins);
						}
					} // for each instance of the statement
				} // for each statement in the method instance
			} // for each instance of the method
		} // for each method
		return cdstmtins;
	} // getAllCDTgtsRelax
	
	/**
	 * retrieve the last use of the specified definition at the given particular statement instance: 
	 * 		only for return and parameter passing induced backward def-use DDs 
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param dvid [in] the variable id of the def queried
	 * @param flag [in] 0 for ret pairing and 1 for parameter pairing
	 * @param lustmtins [out] the statement id and instance number of the last use asked for
	 * @return the variable indicating the last use asked for
	 */
	protected static boolean isParamUse(VariableInfo vinfo) { 
		return vinfo.getVarname().contains("&AP%");// && vinfo.getVarname().substring(0, vinfo.getVarname().lastIndexOf('%')).endsWith("&AP"); 
	}
	protected static boolean isParamDef(VariableInfo vinfo) { 
		return vinfo.getVarname().contains("&FP%");// && vinfo.getVarname().substring(0, vinfo.getVarname().lastIndexOf('%')).endsWith("&FP"); 
	}
	protected static boolean isRetDef(VariableInfo vinfo) { 
		return vinfo.getVarname().contains("&RV@");// && vinfo.getVarname().substring(0, vinfo.getVarname().lastIndexOf('@')).endsWith("&RV"); 
	}
	protected static boolean isRetUse(VariableInfo vinfo) { 
		return vinfo.getVarname().contains("&RT@");// && vinfo.getVarname().substring(0, vinfo.getVarname().lastIndexOf('@')).endsWith("&RT"); 
	}
	protected static int pickParamIdx(VariableInfo vinfo) {
		assert isParamUse(vinfo) || isParamDef(vinfo);
		String strIdx = vinfo.getVarname().substring(vinfo.getVarname().lastIndexOf('%')+1, vinfo.getVarname().lastIndexOf('@'));
		return Integer.parseInt(strIdx);
	}
	protected static String pickMethodName(VariableInfo vinfo) {
		assert isParamUse(vinfo) || isParamDef(vinfo) || isRetDef(vinfo) || isRetUse(vinfo);
		String strIdx = vinfo.getVarname().substring(vinfo.getVarname().lastIndexOf('&')+1);
		return strIdx.substring(strIdx.lastIndexOf('@')+1);
	}
	
	public static VariableInfo getLastUse(TraceReader reader, int stmtid, int ins, int dvid, List<Integer> lustmtins, int flag)
	{
		VariableInfo retvinfo = null;
		VariableInfo tgtDef = getVariableDef(reader, stmtid, ins, dvid);
		if (tgtDef==null) {
			// def not located in the trace: invalid search
			return retvinfo;
		}
		
		/** quickly locate the last 'Use'(Def) in the variable view */
		ListIterator<VariableInfo> iter = reader.getVariableView().listIterator(reader.getVariableView().size());
		int paraIdx1 = 0;
		if (flag==1) {
			paraIdx1 = pickParamIdx(tgtDef);
		}
		String mname = pickMethodName(tgtDef);
		while (iter.hasPrevious()) {
			VariableInfo curv = iter.previous();
			if (curv.getTS() > tgtDef.getTS() || curv.getVarId()>0) {
				continue;
			}
			if (!(isParamUse(curv) || isRetUse(curv))) {
				continue;
			}
			/*
			if (mname.compareToIgnoreCase(pickMethodName(curv))!=0) {
				continue;
			}
			*/
			if ( (flag==0 && isRetUse(curv)) || (flag==1 && isParamUse(curv) && paraIdx1==pickParamIdx(curv))) {
				// relax (leaving out) method-name matching for cases of reflection calls
				if ( (flag==0 && mname.compareToIgnoreCase("ReflectionInvoke")==0) || 
					(flag==1 && pickMethodName(curv).compareToIgnoreCase("ReflectionInvoke")==0) ) {
					retvinfo = curv;
					break;
				}
				
				if (mname.compareToIgnoreCase(pickMethodName(curv))!=0) {
					if (flag==0) {
						/** this could happen if the callee was identified as an 'application callee', on an interface call site for instance, but 
						 * it actually is a library callee at runtime; in such cases, the returned value on the return site won't be 
						 * matched for this use of that retval because the return site, which is in the library code, is not probed
						 * (e.g., org.w3c.dom.NodeList) 
						 */
						if (debugOut) {
							System.err.println("Warning: retval used on stmt " + stmtid + " not found in the callee: tgtdef="+tgtDef + " curv=" +curv);
						}
						return retvinfo;
					}
					if (flag==1) {
						/** this could happen too if the application callee is called only through library code --- for instance, this callee
						 *  is overloading an abstract method in a library class --- while the application code includes only invocations of 
						 *  the caller of that callee (e.g., in nanoxml, ContentReader: int read(bytes[], int, int) is in the application code yet
						 *  never called by any application method, instead it is called by library method java.io.reader.read that is invoked in application code  
						 */
						if (debugOut) {
							System.err.println("Warning: parameter passed onto stmt " + stmtid + " not found in the caller: tgtdef="+tgtDef + " curv=" +curv);
						}
						return retvinfo;
					}
				}
 				assert mname.compareToIgnoreCase(pickMethodName(curv))==0;
 				retvinfo = curv;
				// the first 'used'(defined) variable with smaller time-stamp that is either a parameter use or return value use
				break;
			}
		}
		
		if (null != retvinfo) {
			assert 0 == getVariableLocation(reader, retvinfo, lustmtins);
		}
		
		return retvinfo;
	} // getLastUse
	
	/** class that describes a dynamic slice criteria */
	static public class sliceCriteria {
		int stmtid;
		int stmtins;
		int varid;
		public sliceCriteria(int sid, int sins, int vid) { this.stmtid = sid; this.stmtins = sins; this.varid = vid; }
		public boolean equals(Object o) {
			sliceCriteria osc = (sliceCriteria)o;
			return this.stmtid==osc.stmtid && this.stmtins==osc.stmtins && this.varid==osc.varid;
		}
		public String toString() {
			return "["+stmtid + "," + stmtins + "," + varid + "]";
		}
	}
	
	/** cache criterion whose backward slice has been computed already */
	private static final List<sliceCriteria> cacheCriterion = new ArrayList<sliceCriteria>();
	/** cache statement instance whose last CD has been computed */
	private static final Map<Integer, List<Integer> > cacheLastCDComps = new LinkedHashMap<Integer, List<Integer> >();
	protected static void markSliceComputed(int stmtid, int ins, int vid)
	{
		sliceCriteria sc = new sliceCriteria(stmtid, ins, vid);
		if (!cacheCriterion.contains(sc)) cacheCriterion.add(sc);
	}
	/** check if the backward slice of the particular statement instance has been computed already */
	protected static boolean sliceComputedBefore(int stmtid, int ins, int vid) 
	{
		sliceCriteria sc = new sliceCriteria(stmtid, ins, vid);
		return cacheCriterion.contains(sc);
	}
	protected static void markSliceComputed(Map<Integer, List<Integer> > slicestmt2ins, int stmtid, int ins)
	{
		List<Integer> inses = slicestmt2ins.get(stmtid);
		if (null == inses) {
			inses = new ArrayList<Integer>();
			slicestmt2ins.put(stmtid, inses);
		}
		if (!inses.contains(ins)) inses.add(ins);
	}
	/** check if the backward slice of the particular statement instance has been computed already */
	protected static boolean sliceComputedBefore(Map<Integer, List<Integer> > slicestmt2ins, int stmtid, int ins) 
	{
		List<Integer> inses = slicestmt2ins.get(stmtid);
		if (null == inses) {
			return false;
		}
		return inses.contains(ins);
	}
	
	/** helper for getBackwardSlice: continue backward slicing via two interDDs --- return and parameter passing induced DDs */
	protected static int backtrackViaInterDD(TraceReader reader, int stmtid, int ins, int vid, Map<Integer, List<Integer> > slicestmt2ins)
	{
		VariableInfo tgtDef = getVariableDef(reader, stmtid, ins, vid);
		assert tgtDef != null;
		int flag = -1;
		if (isParamDef(tgtDef)) flag = 1;
		if (isRetDef(tgtDef)) flag = 0;
		if (-1 == flag) {
			return 0;
		}
		
		int ret = 0;
		/*
		List<Integer> backUseVars = ddinfo.getPairedDefs(vid);
		if (null != backUseVars)
		*/ 
		{
			VariableInfo lastUsefinal = null;
			/*
			int lastins = Integer.MIN_VALUE;
			int laststmt = -1;
			for (Integer backUseV : backUseVars) {
				List<Integer> lustmtins = new ArrayList<Integer>();
				VariableInfo lastUse = getLastUse(reader, stmtid, ins, vid, backUseV, lustmtins, ddinfo.isOnReturn(backUseV));
				if (lastUse != null) {
					// keep the most recent one
					if (lustmtins.get(1) > lastins) {
						lastins = lustmtins.get(1);
						lastUsefinal = lastUse;
						laststmt = lustmtins.get(0);
					}
				}
			}
			if (null == lastUsefinal) {
				/** for parameter uses at constructor-call site, we specially inserted their probes *after* the call, so we need special
				 *  instance-comparison constraint to apply: find the actual parameter use of smallest instance *larger* than the instance of
				 *  this formal parameter definition;
				 *  further, if the return of this 
				 *  
				 *   
				assert lastins == Integer.MIN_VALUE;
				assert laststmt == -1;
				for (Integer backUseV : backUseVars) {
					if (ddinfo.isOnReturn(backUseV)) continue;
					List<Integer> lustmtins = new ArrayList<Integer>();
					VariableInfo lastUse = getLastUse(reader, stmtid, ins, vid, backUseV, lustmtins, !ddinfo.isOnReturn(backUseV));
					if (lastUse != null) {
						// keep the most recent one
						if (lustmtins.get(1) > lastins) {
							lastins = lustmtins.get(1);
							lastUsefinal = lastUse;
							laststmt = lustmtins.get(0);
						}
					}
				}	
			}
			
			/** this can be possible: the statically matched DD links may have involved one library call that was mistakenly 
			 * identified as an application call: 
			 * 		example: in org.apache.xml.security.transforms.Transform.getLength(), the return value use at transformElems.getLength() was matched to 
			 * 		the return from org.apache.xml.security.utils.HelperNodeList:: int getLength() during the static analysis, but in fact the runtime 
			 * 		resolved call points to org.apache.xml.dtm.ref.DTMNodeList::getLength() which is in the xalan.jar library, which is not analyzed by Tracer 
			 */
			List<Integer> lustmtins = new ArrayList<Integer>();
			lastUsefinal = getLastUse(reader, stmtid, ins, vid, lustmtins, flag);
			if ( lastUsefinal != null )
			/** sliceComputedBefore check should be commented out here because we need continue tracking along the used variable of this lastUse*/  
			//if (!sliceComputedBefore(slicestmt2ins, laststmt, lastins)) 
			{ 
				//return  getBackwardSlice(reader, laststmt, lastins, lastUsefinal.getVarId(), slicestmt2ins);
				/** return  getBackwardSlice(reader, lustmtins.get(0), lustmtins.get(1), lastUsefinal.getVarId(), slicestmt2ins);*/
				ret += addToSlice(lustmtins.get(0), lustmtins.get(1), slicestmt2ins);
				List<VariableInfo> alluses_atlastdef = getAllUsesAtStmt(reader, lustmtins.get(0));
				assert alluses_atlastdef.contains(lastUsefinal);
				for (VariableInfo vu : alluses_atlastdef) {
					ret += getBackwardSlice(reader, lustmtins.get(0), lustmtins.get(1), vu.getVarId(), slicestmt2ins);
				}
			}
			else if (debugOut) {
				/*
				System.err.println("backtrackViaInterDD: paired def [varid=" + backUseVars + "] for varid=" + vid 
						+ " at statement " + stmtid + "[ins=" + ins + "] not found.");
				*/ 
				System.err.println("backtrackViaInterDD: paired def for varid=" + vid + " at statement " + stmtid + "[ins=" + ins + "] not found.\n");
			}
		}
		return ret;
	}
	
	/**
	 * backward dynamic slic : brute-force implementation	 * 
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @param ins [in] the time stamp of the statement instance for which the query is taken; -1 for the first instance
	 * @param vid [in] the variable id as part of the slicing criterion
	 * @param slicestmt2ins [out] the map of in-slice statement id to the list of all its instance time-stamps 
	 * @return the slice size
	 */
	public static int getBackwardSlice(TraceReader reader, int stmtid, int ins, int vid, Map<Integer, List<Integer> > slicestmt2ins)
	{
		if (sliceComputedBefore(stmtid, ins, vid)) {
			return 0;
		}
		else {
			markSliceComputed(stmtid, ins, vid);
		}
		
		int ret = 0;
		assert slicestmt2ins != null;
		// trivially, slice criterion itself is always included in the slice
		ret += addToSlice(stmtid, ins, slicestmt2ins);
		
		// backwardly search dependees through dynamic DDs
		List<Integer> ldstmtins = new ArrayList<Integer>();
		VariableInfo lastdef = getLastDef(reader, stmtid, ins, Math.abs(vid), ldstmtins);
		/** sliceComputedBefore check should be commented out here because the lastDef can be found at the same statement instance as the Use lies */ 
		if (lastdef != null /*&& !sliceComputedBefore(slicestmt2ins, ldstmtins.get(0), ldstmtins.get(1))*/) {
			ret += addToSlice(ldstmtins.get(0), ldstmtins.get(1), slicestmt2ins);
			
			List<VariableInfo> alluses_atlastdef = getAllUsesAtStmt(reader, ldstmtins.get(0));
			for (VariableInfo vu : alluses_atlastdef) {
				ret += getBackwardSlice(reader, ldstmtins.get(0), ldstmtins.get(1), vu.getVarId(), slicestmt2ins);
			}
			
			/** track along return and parameter passing induced DD links */
			ret += backtrackViaInterDD(reader, ldstmtins.get(0), ldstmtins.get(1), lastdef.getVarId(), slicestmt2ins);
		}
		else if (debugOut) {
			System.err.println("lastDef of varid=" + vid + " at statement " + stmtid + "[ins=" + ins + "] not found.\n");
		}
		
		// backwardly search dependees through dynamic CDs
		/*
		if (sliceComputedBefore(cacheLastCDComps, stmtid, ins)) return ret;
		markSliceComputed(cacheLastCDComps, stmtid, ins);
		List<Integer> lcdins = getLastCDRelax(reader, stmtid, ins);
		if (lcdins != null && !lcdins.isEmpty() && !sliceComputedBefore(slicestmt2ins, lcdins.get(0), lcdins.get(1))) {
			List<Integer> inses = new ArrayList<Integer>();
			inses.add(lcdins.get(1));
			slicestmt2ins.put(lcdins.get(0), inses);
			ret ++;
			
			List<VariableInfo> alluses_atlastcd = getAllUsesAtStmt(reader, lcdins.get(0));
			for (VariableInfo vu : alluses_atlastcd) {
				ret += getBackwardSlice(reader, lcdins.get(0), lcdins.get(1), vu.getVarId(), slicestmt2ins);
			}
		}
		*/
		ret += backtrackViaCD(reader, stmtid, ins, slicestmt2ins);
		
		return ret;
	}
	protected static int addToSlice(int stmtid, int ins, Map<Integer, List<Integer> > slicestmt2ins)
	{
		List<Integer> allins = slicestmt2ins.get(stmtid);
		if (null == allins) {
			allins = new ArrayList<Integer>();
			slicestmt2ins.put(stmtid, allins);
		}
		if (!allins.contains(ins)) {
			allins.add(ins);
			return 1;
		}
		return 0;
	}
	public static int backtrackViaCD(TraceReader reader, int stmtid, int ins, Map<Integer, List<Integer> > slicestmt2ins)
	{
		int ret = 0;
		if (sliceComputedBefore(cacheLastCDComps, stmtid, ins)) return ret;
		markSliceComputed(cacheLastCDComps, stmtid, ins);
		List<Integer> lcdins = getLastCDRelax(reader, stmtid, ins);
		/** sliceComputedBefore check should be commented out here because the lastCD can be the same statement instance as the one queried */
		if (lcdins != null && !lcdins.isEmpty() /*&& !sliceComputedBefore(slicestmt2ins, lcdins.get(0), lcdins.get(1))*/) {
			ret += addToSlice(lcdins.get(0), lcdins.get(1), slicestmt2ins);
			
			List<VariableInfo> alluses_atlastcd = getAllUsesAtStmt(reader, lcdins.get(0));
			for (VariableInfo vu : alluses_atlastcd) {
				ret += getBackwardSlice(reader, lcdins.get(0), lcdins.get(1), vu.getVarId(), slicestmt2ins);
			}
		}
		return ret;
	}
	
	/**
	 * backward dynamic slic : brute-force implementation
	 * @param reader [in] the object of TracerReader with which the underlying trace parsing has been successfully completed
	 * @param stmtid [in] the statement id of the statement for which the query is taken
	 * @return the set of ids of statements in the slice
	 */ 
	public static Set<Integer> getBackwardSlice(TraceReader reader, int stmtid)
	{
		cacheCriterion.clear();
		cacheLastCDComps.clear();
		
		List<VariableInfo> alluses = getAllUsesAtStmt(reader, stmtid);
		List<VariableInfo> alldefs = getAllDefsAtStmt(reader, stmtid);
		Set<Integer> backslice = new LinkedHashSet<Integer>();
		Map<Integer, List<Integer> > slicestmt2ins = new LinkedHashMap<Integer, List<Integer> >();
		
		List<Integer> allStmtIns = getAllStmtInstances(reader, stmtid);
		int ret = 0;
		for (Integer ins : allStmtIns) {
			// search backwardly for all instances of the given statement
			for (VariableInfo vu : alluses) {
				// search backwardly for all variables used at the current instance
				ret += getBackwardSlice(reader, stmtid, ins, vu.getVarId(), slicestmt2ins);
			}
			for (VariableInfo vd : alldefs) {
				if (null==getVariableDef(reader, stmtid, ins, vd.getVarId())) {
					if (debugOut) {
						// this happens for instance when an exception occurs for this particular instance --- def probes are executed after the statement executes
						System.err.println("variable [id=" + vd.getVarId() + "] def not found on statement " + stmtid + " for ins=" + ins);
					}
				}
				else {
					ret += backtrackViaInterDD(reader, stmtid, ins, vd.getVarId(), slicestmt2ins);
				}
			}
			if (alluses.isEmpty()) {
				ret += addToSlice(stmtid, ins, slicestmt2ins);
				ret += backtrackViaCD(reader, stmtid, ins, slicestmt2ins);
			}
		}
		if (0 != ret) {
			assert !slicestmt2ins.isEmpty();
			backslice.addAll(slicestmt2ins.keySet());
		}
		
		return backslice;
	}
}

/* vim :set ts=4 tw=4 tws=4 */
