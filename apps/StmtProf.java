/**
 * File: src/apps/StmtProf.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 09/10/14		hcai		created; for profiling statement execution time 
 */ 
package apps;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import trace.TraceReader;

public class StmtProf {

	static int nExecutions = Integer.MAX_VALUE;
	static boolean debugOut = false;
	static Set<Integer> stmts;
	public static void main(String args[]) throws Throwable {
		if (args.length < 2) {
			System.err.println("Too few arguments: \n\t " +
					"StmtProf traceDir stmt_file [-debug] \n\n");
			return;
		}
		
		String traceDir = args[0]; // tell the directory where execution traces can be accessed
		stmts = readStmts(args[1]);
		
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
			startStmtProf(traceDir);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/** read statements to be profiled from a text file whose name is specified by the sole parameter 
	 *	The format of the text file is as follows:
	 *	stmt_id1,stmt_id2,...,stmt_idn 
	 */
	static Set<Integer> readStmts(String fnCriterion)
	{
		BufferedReader br;
		Set<Integer> sls = new LinkedHashSet<Integer>();
		try {
			br = new BufferedReader(new InputStreamReader(new FileInputStream(fnCriterion)));
			String ts = br.readLine();
			while(ts != null) {
				if (ts.trim().length()<1) { 
					ts = br.readLine();
					continue;
				}
				
				sls.add(Integer.parseInt(ts.trim()));
				ts = br.readLine();
			}
			br.close();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		return sls;
	}
	
	public static void startStmtProf(String traceDir) {
		int tId;
		
		for (tId = 1; tId <= nExecutions; ++tId) {
			try {
				if (debugOut) {
					System.out.println("statement execution time for test " + tId + ": ");
				}
				
				getSliceExecTime(traceDir, tId, stmts);
			}
			catch (Exception e) {
				e.printStackTrace();
				break;
			}
		}
	}
	
	public static Long getSliceExecTime(String traceDir, int tId, Set<Integer> slice) throws Exception {
		Long costTotal = 0L;
		try {
			
			String fnTrace = traceDir  + File.separator + "test" + tId + ".em";
	
			/**
			 * Prepare the trace reader
			 * */
			// to handle multiple-file trace for a single test case
			int g_traceCnt = 0;
			while (true) {
				String curfnStmtProf = fnTrace + 'p' + (g_traceCnt>0?g_traceCnt:""); 
				if (!new File(curfnStmtProf).exists()) {
					// all segments have been processed
					break;
				}
				
				g_traceCnt ++;
				
				TraceReader treader = new TraceReader();
				treader.setStmtProf(curfnStmtProf);
				treader.readStmtProf(false/*debugOut*/);
				
				// obtain execution time of statements in the slice (for all instances of each statement)
				for (Integer sid : slice) {
					List<Long> tt = treader.getStmtProfData().get(sid);
					if (null == tt) {
						System.err.println("no execution time profiling data found for statement " + sid + " in " + curfnStmtProf);
						continue;
					}
					System.out.println("stmt_id " + sid + " execution-time-in-ns " + tt);
					for (Long t : tt) {
						costTotal += t;
					}
				}
			}
		}
		catch (Exception e) {
			throw e;
		}
		return costTotal;
	}
}
