/**
 * File: src/trace/TraceReader.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/25/14		hcai		created; read trace per test case, possibly including multiple segments, from disk file(s)
 * 06/09/14		hcai		make TraceReader accessible outside
 * 07/12/14		hcai		index by variable time-stamp to speed up search in the trace for lastDef/lastCD/...
 * 08/17/14		hcai		load statement execution time profiling data if found
*/
package trace;

import java.io.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.zip.GZIPInputStream;

import com.VariableInfo;

public class TraceReader {
	/* the full sequence of method events */
	protected Map<Integer, Integer> EMSeq = new LinkedHashMap<Integer, Integer>();
	/* the map from index to method signature associated with the full sequence of method events */
	protected final Map<Integer, String> MethodMap = new LinkedHashMap<Integer, String>();
	
	/* the central map of the trace */
	private Map< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>> traceCache = 
		new LinkedHashMap< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>>();
	
	/* variable index --- a perspective of the entire trace cache */
	private List< VariableInfo > variableView = new ArrayList<VariableInfo> (); 
	
	/* the file holding the method event trace */
	protected String fnMethodEventTrace = "";
	/* the file holding the 'whole' execution trace */
	protected String fnStateTrace = "";
	
	/** a map from method signature to its index */
	protected final Map< String, Integer > method2idx = new LinkedHashMap<String, Integer>();
	
	/* the statement execution time profiling report */
	protected Map<Integer, List<Long> > stmtProfCache = new LinkedHashMap<Integer, List<Long>>();
	/* the file holding the profiling result */
	protected String fnStmtProf = "";
	
	public TraceReader() {
		super();
	}
	
	// accessories
	public final Map< Integer, String > getIdx2Method() { return MethodMap; }
	public final Map< String, Integer > getMethod2Idx() { return method2idx; }
	public final Map< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>> getStructuredTrace() { return traceCache; }
	public final Map<Integer, Integer> getEMSequence() { return EMSeq; }
	public final List<VariableInfo> getVariableView() { return variableView; }
	
	public final Map<Integer, List<Long> > getStmtProfData() { return stmtProfCache; }
	
	public void setMethodTrace(String _fnMethodEventTrace) {
		fnMethodEventTrace = _fnMethodEventTrace;
	}
	public void setStateTrace(String _fnStateEventTrace) {
		fnStateTrace = _fnStateEventTrace;
	}
	public void setStmtProf(String _fnStmtProf) {
		fnStmtProf = _fnStmtProf;
	}
	
	@Override public String toString() {
		return "[Trace Reader] " + super.toString(); 
	}
	
	public boolean isEmpty() {
		return EMSeq.isEmpty() || traceCache.isEmpty();
	}
	public void reset() {
		EMSeq.clear();
		traceCache.clear();
		
		method2idx.clear();
	}
	
	public boolean hasStmtProfData() {
		return !stmtProfCache.isEmpty();
	}
		
	/** load the method event trace from the given source */
	protected int loadEMSequence(String fnSource) {
		EMSeq.clear();
		MethodMap.clear();

		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			GZIPInputStream gis = new GZIPInputStream(fis);
			int len = 1024;
			int ziplen = (int)new File(fnSource).length();
			byte[] bs = new byte[ziplen*1024]; // Gzip won't have more than 1024 compression ratio for the binary data
			int off = 0;
			while (gis.available()!=0) {
				off += gis.read(bs, off, len);
			}
			gis.close();
			fis.close();

			ByteArrayInputStream bis = new ByteArrayInputStream(bs);
			
			//ObjectInputStream ois = new ObjectInputStream(fis);
			ObjectInputStream ois = new ObjectInputStream(bis);
			
			Map<String,Integer> EAmethod2idx = new LinkedHashMap<String,Integer>();
			@SuppressWarnings("unchecked")
			LinkedHashMap<String,Integer> readObject1 = (LinkedHashMap<String,Integer>) ois.readObject();
			EAmethod2idx = readObject1;
			for (Map.Entry<String, Integer> en : EAmethod2idx.entrySet()) {
				// create an inverse map for facilitating quick retrieval later on
				MethodMap.put(en.getValue(), en.getKey());
			}
			method2idx.putAll(EAmethod2idx);
			
			@SuppressWarnings("unchecked")
			LinkedHashMap<Integer, Integer> readObject2 = (LinkedHashMap<Integer, Integer>) ois.readObject();
			EMSeq = readObject2;
			
			ois.close();
			bis.close();
			// --
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the given input method trace file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to LinkedHashMap<Integer, String>!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	}
	
	/** load the central whole execution trace from the given source */
	protected int loadStateTrace(String fnSource) {
		traceCache.clear();
		MethodMap.clear();

		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			GZIPInputStream gis = new GZIPInputStream(fis);
			int len = 1024;
			int ziplen = (int)new File(fnSource).length();
			byte[] bs = new byte[ziplen*1024]; // Gzip won't have more than 1024 compression ratio for the binary data
			int off = 0;
			int nr = 0;
			while (gis.available()!=0) {
				nr = gis.read(bs, off, len);
				if (-1 == nr) break;
				off += nr;
			}
			gis.close();
			fis.close();

			ByteArrayInputStream bis = new ByteArrayInputStream(bs);
			
			//ObjectInputStream ois = new ObjectInputStream(fis);
			ObjectInputStream ois = new ObjectInputStream(bis);
			
			/** read the method->idx map */ 
			Map<String,Integer> EAmethod2idx = new LinkedHashMap<String,Integer>();
			@SuppressWarnings("unchecked")
			LinkedHashMap<String,Integer> readObject1 = (LinkedHashMap<String,Integer>) ois.readObject();
			EAmethod2idx = readObject1;
			for (Map.Entry<String, Integer> en : EAmethod2idx.entrySet()) {
				// create an inverse map for facilitating quick retrieval later on
				MethodMap.put(en.getValue(), en.getKey());
			}
			
			/** read the trace cache */
			@SuppressWarnings("unchecked")
			Map< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>> readObject2 = 
				(LinkedHashMap< Integer, Map<Integer, Map< Integer, Map<Integer, List<VariableInfo>>>>>) ois.readObject();
			traceCache = readObject2;
			
			ois.close();
			bis.close();
			// --
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the given input state trace file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to LinkedHashMap< Integer, Map<Integer, Map< Integer, Map<Integer, List<Integer>>>>>!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	}
	
	/** load the statement level execution cost profiling result from the given source */
	protected int loadStmtProf(String fnSource) {
		stmtProfCache.clear();

		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			GZIPInputStream gis = new GZIPInputStream(fis);
			int len = 1024;
			int ziplen = (int)new File(fnSource).length();
			byte[] bs = new byte[ziplen*1024]; // Gzip won't have more than 1024 compression ratio for the binary data
			int off = 0;
			int nr = 0;
			while (gis.available()!=0) {
				nr = gis.read(bs, off, len);
				if (-1 == nr) break;
				off += nr;
			}
			gis.close();
			fis.close();

			ByteArrayInputStream bis = new ByteArrayInputStream(bs);
			
			//ObjectInputStream ois = new ObjectInputStream(fis);
			ObjectInputStream ois = new ObjectInputStream(bis);
			
			/** read the statement execution time profiling cache */
			@SuppressWarnings("unchecked")
			Map< Integer, List<Long> > readObject =  (LinkedHashMap< Integer, List<Long>>) ois.readObject();
			stmtProfCache = readObject;
			
			ois.close();
			bis.close();
			// --
		}
		catch (FileNotFoundException e) {
			System.err.println("Failed to locate the given input stmtProf file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to LinkedHashMap< Integer, List<Long> >!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	}
	
	/** build variable index by time-stamp order */
	protected void createVariableView() {
		if (isEmpty()) return;
		for (Integer mid : this.getStructuredTrace().keySet()) {
			for (Integer mins : this.getStructuredTrace().get(mid).keySet()) {
				for (Integer sid : this.getStructuredTrace().get(mid).get(mins).keySet()) {
					for (Integer stmtins : this.getStructuredTrace().get(mid).get(mins).get(sid).keySet()) {
						for (VariableInfo vinfo : this.getStructuredTrace().get(mid).get(mins).get(sid).get(stmtins)) {
							variableView.add(vinfo);	
						}
					}
				}
			}
		}
		Collections.sort(variableView);
	}
		
	public int readTrace(boolean debugOut) {
		// 1. load the method event trace
		if (null == fnMethodEventTrace || fnMethodEventTrace.length() < 1 ||
				null == fnStateTrace || fnStateTrace.length() < 1) {
			// trace not associated yet
			return -1;
		}
		
		Integer preMethod = null;
		
		// to handle multiple-file trace for a single test case
		int g_traceCnt = 0;
		while (true) {
			String curfnMethodEventTrace = fnMethodEventTrace + (g_traceCnt>0?g_traceCnt:"");
			String curfnStateTrace = fnStateTrace + (g_traceCnt>0?g_traceCnt:"");
			if (!new File(curfnMethodEventTrace).exists() || !new File(curfnStateTrace).exists()) {
				// all segments have been processed
				break;
			}
			g_traceCnt ++;
			
			if (0 != loadEMSequence(curfnMethodEventTrace)) {
				// method trace not loaded successfully
				return -2;
			}
			if (0 != loadStateTrace(curfnStateTrace)) {
				// state trace not loaded successfully
				return -3;
			}
			createVariableView();
			
			// - For DEBUG only
			if (debugOut) {
				System.out.println("===== method indexing map =====");
				System.out.println(MethodMap);
				System.out.println("===== The current execution trace under use [loaded from the call sequence] =====");
				TreeMap<Integer, Integer> treeA = new TreeMap<Integer, Integer> ( EMSeq );
				System.out.println(treeA);
			}
			
			// 2. scan the method event trace
			for (Map.Entry<Integer, Integer> _event : EMSeq.entrySet()) {
				Integer va = _event.getValue();
				if (va == Integer.MIN_VALUE || va == Integer.MAX_VALUE) {	
					// these are just two special events marking start and termination of the run
					continue;
				}
				
				String emstr = MethodMap.get(Math.abs(va));
				Integer em = method2idx.get(emstr);
				
				//boolean isEnterEvent = va < 0;
							
				if (null == preMethod || preMethod.equals(em)) {
					// nothing to do with the first event
					preMethod = em;
					continue;
				}
				preMethod = em;
				
			} // for each method event in currently examined execution trace
		} // for each trace segment file
		
		return 0;
	}
	
	public int readStmtProf(boolean debugOut) {
		if (null == fnStmtProf || fnStmtProf.length() < 1) {
			// profiling data not associated yet
			return -1;
		}
		
		// to handle multiple-file trace for a single test case
		int g_traceCnt = 0;
		while (true) {
			
			String curfnStmtProf = fnStmtProf + (g_traceCnt>0?g_traceCnt:"");
			if (!new File(curfnStmtProf).exists()) {
				break;
			}
			
			g_traceCnt ++;
			
			if (0 != loadStmtProf(curfnStmtProf)) {
				// profiling data not loaded successfully
				return -2;
			}
			
			// - For DEBUG only
			if (debugOut) {
				System.out.println("===== statement execution time profiling result (nano seconds) =====");
				for (Map.Entry<Integer, List<Long>> en : stmtProfCache.entrySet()) {
					System.out.println("\t" + en.getKey() + "\t" + en.getValue());
				}
			}
		} // for each profiling-result segment file
		
		return 0;
	}
	
} // definition of TraceReader

/* vim :set ts=4 tw=4 tws=4 */
