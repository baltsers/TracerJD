/**
 * File: src/apps/StmtCov.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 08/29/14		hcai		created; for reporting per-test statement coverage
 */ 
package apps;

import java.io.File;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import deam.StmtIdReader;

import trace.TraceReader;

public class StmtCov {

	static int nExecutions = Integer.MAX_VALUE;
	static boolean debugOut = false;
	
	static StmtIdReader stmtReader = new StmtIdReader();
	
	public static void main(String args[]) throws Throwable {
		if (args.length < 1) {
			System.err.println("Too few arguments: \n\t " +
					"StmtCov traceDir [nTraces] [-debug] \n\n");
			return;
		}
		
		String traceDir = args[0]; // tell the directory where execution traces can be accessed
		if (args.length > 1) {
			nExecutions = Integer.parseInt(args[1]);
		}
		
		if (args.length > 2) {
			debugOut = args[2].equalsIgnoreCase("-debug");
		}
		
		if (debugOut) {
			System.out.println("Try to read [" + (-1==nExecutions?"All available":nExecutions) + "] traces in "	+ traceDir);
		}
		
		// prepare for dynamic slicing
		trace.TraceAnalysis.debugOut = debugOut;
		trace.TraceAnalysis.loadAllStaticInfo(traceDir);
		stmtReader.setFile(traceDir+File.separator+"stmtids.out");
		
		try {
			startStmtCov(traceDir);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void startStmtCov(String traceDir) {
		int tId;
		int nTotal = stmtReader.getAllStmts().size();
		DecimalFormat df = new DecimalFormat("#.##");
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			try {
				// obtain execution slice
				Set<Integer> execSlice = new LinkedHashSet<Integer>(getSingleExecSlice(traceDir, tId));
				int szES = execSlice.size();
				System.out.println("statement coverage of test " + tId + ": " + szES + "/" + nTotal + "="
						+ df.format(szES*1.0/nTotal*100) + "%");
			}
			catch (Exception e) {
				e.printStackTrace();
				break;
			}
		}
	}
	
	public static List<Integer> getSingleExecSlice(String traceDir, int tId) throws Exception {
		List<Integer> stmtIds = new ArrayList<Integer>();
		try {
			
			String fnTrace = traceDir  + File.separator + "test" + tId + ".em";
			if (debugOut) {
				System.out.println("\nProcessing execution trace for test no. " + tId);
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
				treader.readTrace(debugOut);
				for (Integer mid : treader.getStructuredTrace().keySet()) {
					// search all methods
					for (Integer mins : treader.getStructuredTrace().get(mid).keySet()) {
						// search all instances of each method
						for (Integer sid : treader.getStructuredTrace().get(mid).get(mins).keySet()) {
							if(!stmtIds.contains(sid)){
								stmtIds.add(sid);
							}
						}
					}
				}
			}
		}
		catch (Exception e) {
			throw e;
		}
		return stmtIds;
	}
}
