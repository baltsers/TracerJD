/**
 * File: src/apps/DynSlicer.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/10/14		hcai		created; for backward dynamic slicing from a given criteria
 * 06/16/14		hcai		reached the first draft version
 * 06/25/14		hcai		done first round of debugging and reached the working version  
 * 08/17/14		hcai		stable working version
 */ 
package apps;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import deam.StmtIdReader;

import trace.TraceReader;

public class DynSlicer {

	static int nExecutions = Integer.MAX_VALUE;
	static boolean debugOut = false;
	static Map<Integer, List<Integer>> test2criterion;
	
	static StmtIdReader stmtReader = new StmtIdReader();
	
	public static void main(String args[]) throws Throwable {
		if (args.length < 2) {
			System.err.println("Too few arguments: \n\t " +
					"DynSlicer traceDir CriterionFile [nTraces] [-debug] \n\n");
			return;
		}
		
		String traceDir = args[0]; // tell the directory where execution traces can be accessed
		test2criterion = new LinkedHashMap<Integer, List<Integer>>();
		String criterionFile = args[1]; // tell the file in which per-test slicing criterion are listed
		test2criterion = readCriterion(criterionFile);
		
		if (args.length > 2) {
			nExecutions = Integer.parseInt(args[2]);
		}
		
		if (args.length > 3) {
			debugOut = args[3].equalsIgnoreCase("-debug");
		}
		
		if (debugOut) {
			System.out.println("Try to read [" + (-1==nExecutions?"All available":nExecutions) + "] traces in "	+ traceDir);
		}
		
		// prepare for dynamic slicing
		trace.TraceAnalysis.debugOut = debugOut;
		trace.TraceAnalysis.loadAllStaticInfo(traceDir);
		
		try {
			startDynSlicer(traceDir);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/** read slicing criterion per test case from a text file whose name is specified by the sole parameter 
	 *	The format of the text file is as follows:
	 *	test_id stmt_id1,stmt_id2,...,stmt_idn 
	 */
	static Map<Integer, List<Integer>> readCriterion(String fnCriterion)
	{
		BufferedReader br;
		Map<Integer, List<Integer>> test2sc = new LinkedHashMap<Integer, List<Integer>>();
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnCriterion)));
			String ts = br.readLine();
			while(ts != null){
				if (ts.trim().length()<3) { 
					ts = br.readLine();
					continue;
				}
				String[] segs1 = ts.split("\\s+",2);
				assert segs1.length >=2;
				int test_id = Integer.parseInt(segs1[0]);
				List<Integer> sc = test2sc.get(test_id);
				if (null == sc) {
					sc = new ArrayList<Integer>();
					test2sc.put(test_id, sc);
				}
				String[] segs2 = segs1[1].split(",|;|:");
				assert segs2.length >= 1;
				for (String sid : segs2) {
					sc.add(Integer.parseInt(sid.trim()));
				}
				
				ts = br.readLine();
			}
			br.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		return test2sc;
	}
	
	public static void startDynSlicer(String traceDir) {
		int tId;
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			try {
				
				if (test2criterion.get(tId).isEmpty()) {
					System.out.println("\tslicing criterion for test No. " + tId + " is none!");
					continue;
				}
				if (debugOut) {
					System.out.println("dyn. slice criterion for test " + tId + ": " + test2criterion.get(tId));
				}
				
				// obtain union dynamic slice for all output points
				Set<Integer> dynSlice = getDynSliceSingleTrace(traceDir, tId);
				
				int szDS = dynSlice.size();
				System.out.println("dyn. slice for test " + tId + "[size=" + szDS + "]:\n " + dynSlice);
			}
			catch (Exception e) {
				e.printStackTrace();
				break;
			}
		}
	}
	
	public static Set<Integer> getDynSliceSingleTrace(String traceDir, int tId) throws Exception {
		Set<Integer> dynSlice = new LinkedHashSet<Integer>();
		try {
			
			String fnTrace = traceDir  + File.separator + "test" + tId + ".em";
			if (debugOut) {
				System.out.println("\nProcessing execution trace for test no. " + tId + 
						" - criterion= " + test2criterion.get(tId));
			}
	
			/**
			 * Prepare the trace reader
			 * */
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
				treader.readTrace(false/*debugOut*/);
				
				// obtain dynamic slices for all criterion (output points) and unionize them
				List<Integer> sc = test2criterion.get(tId);
				if (sc == null) {
					System.err.println("slicing criterion for test No. " + tId + " were not found");
					return dynSlice;
				}
				for (int sid : sc) {
					dynSlice.addAll( trace.TraceAnalysis.getBackwardSlice(treader, sid) );
				}
			}
		
		}
		catch (Exception e) {
			throw e;
		}
		return dynSlice;
	}
}
