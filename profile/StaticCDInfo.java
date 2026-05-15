/**
 * File: src/profile/StaticCDInfo.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 03/28/14		hcai		created; compute static control dependencies for dynamic CD tracing
 * 04/10/14		hcai		debugged through xmlsec and jmeter after schedule and nanoxml
 * 04/17/14		hcai		fixed more issues found when testing with the entire skeleton
 * 05/28/14		hcai		fixed a few issues when testing the basic trace queries in the post-processor 
*/
package profile;

import java.io.*;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import dua.global.ProgramFlowGraph;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;

import Diver.SVTEdge;
import Diver.SVTNode;
import Diver.StaticCDGraphEx;
import Diver.StaticInterCDGraphEx;

/** the static interprocedural control dependence graph (ICDG), from which all static CD info can be retrieved 
 */
public class StaticCDInfo extends StaticInterCDGraphEx implements Serializable {
	/* all reachable application methods - retrieve in advance for efficient later accesses */
	transient static Set<SootMethod> reachableMethods;
	
	/** this ctor is used for creating the instance from deserialization during post-processing phase */
	public StaticCDInfo() {
		exceptionUnits = new BitSet();
		src2tgts = new LinkedHashMap<Integer, BitSet>();
		tgt2srcs = new LinkedHashMap<Integer, BitSet>();
		reachableMethods = null;
	}
	/** this ctor is used for creating the instance by static analysis */
	public StaticCDInfo(boolean debugOut) {
		super(false/*debugOut*/);
		super.turnSymbolicCD(true);
		super.turnHolisticCDG(true);
		init();
		reachableMethods = null;
	}
	
	@Override public String toString() {
		return "[Static InterCDGraph] " + super.toString();
	}
	
	/** build the ICDG by reusing all mcia-Utils originally developed for Diver */
	protected int buildGraph(boolean debugOut) throws Exception {
		if (!(CDNodes.isEmpty() && CDEdges.isEmpty())) {
			// already done before
			return 0;
		}
		
		reachableMethods = new LinkedHashSet<SootMethod>(); 
		reachableMethods.addAll(ProgramFlowGraph.inst().getReachableAppMethods());
		
		/** traverse all classes and methods to computer the CDG per method */
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
				if (!reachableMethods.contains(sMethod)) {
					// skip unreachable methods
					//continue;
				}
				/** particularly for Dacapo FOP */
				/*
				if ( (sClass.getName().contains("org.apache.fop.text.linebreak.LineBreakUtils") ||
						sClass.getName().contains("org.apache.fop.fonts.Glyphs") ||
						sClass.getName().contains("org.apache.fop.fonts.base14.Courier") ||
						sClass.getName().contains("org.apache.fop.fonts.CodePointMapping"))
						&& sMethod.getName().contains("init") ) {
					continue;
				}
				*/
				if (sMethod.getActiveBody().getUnits().size() > 2000) {
					System.err.println(new Exception().getStackTrace()[0].getMethodName() + ": " + 
							sMethod.getSignature() + " skipped because of its oversize.");
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				String meId = sMethod.getSignature();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\nCDG construction: now processing method " + meId + "...");
				}
				
				/* intraprocedural control dependencies */
				final StaticCDGraphEx CDGEx = new StaticCDGraphEx();
				CDGEx.turnDebug(false/*debugOut*/);
				CDGEx.turnSymbolicCD(false);
				CDGEx.setCurDefSet(new ArrayList<SVTNode>());
				CDGEx.compuateIntraproceduralCDs(sMethod, null);
					
				/* Preparation for computing Inter-procedural control dependencies */
				this.setMethodCDG(sMethod, CDGEx);
			}
		}
		
		// -- DEBUG
		if (debugOut) {
			System.out.println("\nICDG construction: now computing interprocedural CDs......");
		}
		this.computeAllInterCDs();
		
		return 0;
	} // buildGraph
	
	static Map<Stmt, Integer> stmtIds = null;
	/** mark which statements are in exceptional blocks --- catch/finally blocks */
	transient BitSet exceptionUnits;
	/** map from a statement to all statements that depend on it */
	transient Map<Integer, BitSet> src2tgts;
	/** map from a statement to all its incoming branch sources */
	transient Map<Integer, BitSet> tgt2srcs;
	
	private void init() {
		if (stmtIds == null) {
			stmtIds = StmtMapper.getWriteGlobalStmtIds();
		}
		exceptionUnits = new BitSet(stmtIds.size());
		src2tgts = new LinkedHashMap<Integer, BitSet>();
		tgt2srcs = new LinkedHashMap<Integer, BitSet>();
	}
	
	/** build the static CD info --- fill the preceding data structures */
	protected int computeCDInfo() {
		if (!(src2tgts.isEmpty() && tgt2srcs.isEmpty())) {
			// already done before
			return 0;
		}
		
		try {
			buildGraph(debugOut);
		} catch (Exception e) {
			e.printStackTrace();
			return -1;
		}
			
		for (SVTNode sn : this.CDNodes) {
			Integer icur = stmtIds.get(sn.getStmt());
			if (null == icur) {
				// skip those "virtual nodes" like ENTRY/EXIT/AugmentedUnit
				continue; 
			}
			
			// traverse outgoing edges from the current node
			BitSet bstgts = src2tgts.get(icur);
			if (null == bstgts) {
				bstgts = new BitSet(stmtIds.size());
			}
			if (this.getOutCDGEdges(sn) != null) {
				for (SVTEdge e : this.getOutCDGEdges(sn)) {
					Integer itgt = stmtIds.get(e.getTarget().getStmt());
					if (null == itgt) {
						// skip those "virtual nodes" like ENTRY/EXIT/AugmentedUnit
						continue; 
					}
					bstgts.set(itgt);
				}
			}
			src2tgts.put(icur, bstgts);
			
			// traverse incoming edges to the current node
			BitSet bssrcs = tgt2srcs.get(icur);
			if (null == bssrcs) {
				bssrcs = new BitSet(stmtIds.size());
			}
			if (this.getInCDGEdges(sn) != null) {
				for (SVTEdge e : this.getInCDGEdges(sn)) {
					Integer isrc = stmtIds.get(e.getSource().getStmt());
					if (null == isrc) {
						// skip those "virtual nodes" like ENTRY/EXIT/AugmentedUnit
						continue; 
					}
					bssrcs.set(isrc);
				}
			}
			tgt2srcs.put(icur, bssrcs);
			
			// exceptional unit marking
			if (ProgramFlowGraph.inst().getNode(sn.getStmt()).isInCatchBlock()) {
				exceptionUnits.set(icur);
			}
		}
		
		return 0;
	} // computeCDInfo
	
	/** accessories */
	// retrieve the ids of statements that are control dependent on the given statement
	public List<Integer> getCDTgts(Integer icur) {
		computeCDInfo();
		assert src2tgts.containsKey(icur);
		
		List<Integer> itgts = new ArrayList<Integer>();
		/*
		for (int idx = 0, curbitidx=0; idx < src2tgts.get(icur).cardinality(); idx++) {
			curbitidx = src2tgts.get(icur).nextSetBit(curbitidx);
			itgts.add(curbitidx);
		}
		*/
		for(int i=src2tgts.get(icur).nextSetBit(0); i>=0; i=src2tgts.get(icur).nextSetBit(i+1)) { 
			// operate on index i here
			itgts.add(i);
		}
		
		return itgts; 
	}
	
	// retrieve the ids of statements on which the given statement are control dependent
	public List<Integer> getCDSrcs(Integer icur) {
		computeCDInfo();
		assert tgt2srcs.containsKey(icur);
		
		List<Integer> isrcs = new ArrayList<Integer>();
		for(int i=tgt2srcs.get(icur).nextSetBit(0); i>=0; i=tgt2srcs.get(icur).nextSetBit(i+1)) { 
			// operate on index i here
			isrcs.add(i);
		}
		
		return isrcs; 
	}
	
	// determine if the given statement is an exceptional unit
	boolean isExceptionalUnit(Integer icur) {
		computeCDInfo();
		assert exceptionUnits.size() > icur;
		
		return exceptionUnits.get(icur);
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	///////////////////////////////////////////////////////////////////////////////////////////////////
	private static final long serialVersionUID = 0x438211DE;
	
    /** Save the state of the <tt>StaticCDInfo</tt> instance to a stream (i.e., serialize it) */
    private void writeObject(java.io.ObjectOutputStream s)  throws IOException
    {
        // Write out any hidden stuff
        s.defaultWriteObject();

        //System.out.println("done writing default objects: sizes src2tgts=" + src2tgts.size() + " tgt2srcs=" + tgt2srcs.size() + " exceptionUnits=" + exceptionUnits.size());
        // the real contents to be serialized
        s.writeObject(this.src2tgts);
        s.writeObject(this.tgt2srcs);
        s.writeObject(this.exceptionUnits);
        
        s.flush();
    }

    /** Load the state of the <tt>StaticCDInfo</tt> instance from a stream (i.e., deserialize it) */
    @SuppressWarnings("unchecked")
	private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException
    {
        // Read any hidden stuff
        s.defaultReadObject();
        
        // Load the real contents
        this.src2tgts = (Map<Integer, BitSet>) s.readObject();
        this.tgt2srcs = (Map<Integer, BitSet>) s.readObject();
        this.exceptionUnits = (BitSet) s.readObject();
        // -
    }
    
    /** serailize the instance of this to a given external file */ 
	public int SerializeToFile_compress(String fnTarget) {
		/* serialize for later deserialization in the post-processing phase */
		if ( fnTarget.isEmpty() ) {
			return -1;
		}
		
		computeCDInfo();
		FileOutputStream fos;
		try {
			ByteArrayOutputStream bos = new ByteArrayOutputStream();
			fos = new FileOutputStream(fnTarget);
			GZIPOutputStream goos = new GZIPOutputStream(fos);
			ObjectOutputStream oos = new ObjectOutputStream(bos);
			
			oos.writeObject(this);
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
			return -2;
		}
		finally {
		}
		
		return 0;
	} // SerializeToFile_compress
	
	 /** serailize the instance of this to a given external file */ 
	public int SerializeToFile(String fnTarget) {
		/* serialize for later deserialization in the post-processing phase */
		if ( fnTarget.isEmpty() ) {
			return -1;
		}
		
		computeCDInfo();
		FileOutputStream fos;
		try {
			RandomAccessFile raf = new RandomAccessFile(fnTarget, "rw");
			fos = new FileOutputStream(raf.getFD());
			//ByteArrayOutputStream bos = new ByteArrayOutputStream();
			//GZIPOutputStream goos = new GZIPOutputStream(fos);
			ObjectOutputStream oos = new ObjectOutputStream(fos/*bos*/);
			
			oos.writeObject(this);
			oos.flush();
			oos.close();
			
			//goos.write(bos.toByteArray());
			//goos.flush();
			//goos.close();
			
			fos.flush();
			fos.close();
		}
		catch (Exception e) {
			e.printStackTrace();
			return -2;
		}
		finally {
		}
		
		return 0;
	} // SerializeToFile
	
    /** instantiate an object of this by reading an external file */
	public int DeserializeFromFile_compress(String fnSource) {
		FileInputStream fis;
		try {
			fis = new FileInputStream(fnSource);
			
			GZIPInputStream gis = new GZIPInputStream(fis);
			int len = 1024;
			int ziplen = (int)new File(fnSource).length();
			byte[] bs = new byte[ziplen*1024]; // Gzip won't have more than 50 compression ratio for the binary data
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

			ObjectInputStream ois = new ObjectInputStream(bis);
			
			StaticCDInfo readObject = (StaticCDInfo) ois.readObject();
			this.src2tgts.clear();
			this.src2tgts.putAll(readObject.src2tgts);
			this.tgt2srcs.clear();
			this.tgt2srcs.putAll(readObject.tgt2srcs);
			this.exceptionUnits.clear();
			this.exceptionUnits.or(readObject.exceptionUnits);
			
			ois.close();
			bis.close();
			// --
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the given input file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to StaticCDInfo!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	} // DeserializeFromFile_compress
	
	public int DeserializeFromFile(String fnSource) {
		FileInputStream fis;
		try {
			RandomAccessFile raf = new RandomAccessFile(fnSource, "r");
			fis = new FileInputStream(raf.getFD());
			ObjectInputStream ois = new ObjectInputStream(fis);
			
			StaticCDInfo readObject = (StaticCDInfo) ois.readObject();
			this.src2tgts.clear();
			this.src2tgts.putAll(readObject.src2tgts);
			this.tgt2srcs.clear();
			this.tgt2srcs.putAll(readObject.tgt2srcs);
			this.exceptionUnits.clear();
			this.exceptionUnits.or(readObject.exceptionUnits);
			
			ois.close();
			fis.close();
			// --
		}
		catch (FileNotFoundException e) { 
			//System.err.println("Failed to locate the given input file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			//System.err.println("Failed to cast the object deserialized to StaticCDInfo!");
			return -2;
		}
		catch (IOException e) {
			throw new RuntimeException(e); 
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		return 0;
	} // DeserializeFromFile
	
	/**
	 * for debugging purposes, list all src->tgts and tgt<-srcs mappings
	 */
	public int dumpCDMappings(PrintStream os) {
		computeCDInfo();
		
		os.println("[src->tgts mapping]");
		for (int sid = 0; sid < stmtIds.size(); sid++) {
			if (!src2tgts.containsKey(sid)) { continue; }
			List<Integer> cdtgts = getCDTgts(sid);
			if (cdtgts.isEmpty()) { continue; }
			
			os.print(sid + " -> ");
			for (Integer tgtid : cdtgts) {
				os.print(tgtid + " ");
			}
			os.println();
		}
		
		os.println("[tgt<-srcs mapping]");
		for (int sid = 0; sid < stmtIds.size(); sid++) {
			if (!tgt2srcs.containsKey(sid)) { continue; }
			List<Integer> cdsrcs = getCDSrcs(sid);
			if (cdsrcs.isEmpty()) { continue; }
			
			os.print(sid + " <- ");
			for (Integer srcid : cdsrcs) {
				os.print(srcid + " ");
			}
			os.println();
		}
		
		os.println("[exceptional units]");
		for(int i=exceptionUnits.nextSetBit(0); i>=0; i=exceptionUnits.nextSetBit(i+1)) { 
			// operate on index i here
			os.print(i + " ");
		}
		os.println();
		
		return 0;
	} // dumpCDMappings
	
} // definition of StaticCDInfo

/* vim :set ts=4 tw=4 tws=4 */
