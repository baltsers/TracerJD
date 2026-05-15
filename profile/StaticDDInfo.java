/**
 * File: src/profile/StaticDDInfo.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/12/14		hcai		created; compute static data dependencies linking 
 *							(1) returned value and its use, and (2) actual parameter to formal parameter
 * 06/13/14		hcai		created constant variables for constant return value and constant argument
 * 06/18/14		hcai		debugged/tested, and now working, for XML-security NanoXML and Schedule1: model stringConstant at return sites 
*/
package profile;

import java.io.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import com.Utils;

import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.CFGDefUses;
import dua.method.CallSite;
import dua.method.ReachableUsesDefs;
import dua.method.CFG.CFGNode;
import dua.method.CFGDefUses.Variable;
import dua.method.CFGDefUses.CSArgVar;
import dua.method.CFGDefUses.ReturnVar;

import soot.*;
import soot.jimple.*;

/** compute the static interprocedural data dependencies between returned value and use, and actual and formal parameters  
 *		- def/use on these interprocedural DDs can not simply be matched by variable id or base object address/array index
 */
public class StaticDDInfo implements Serializable {
	/* all reachable application methods - retrieve in advance for efficient later accesses */
	transient private Set<SootMethod> reachableMethods;
	transient private boolean debugOut = false;
	
	/** map from a def to use for parameter-passing induced DDs*/
	private Map<Integer, List<Integer>> paraDef2Use;
	private Map<Integer, List<Integer>> paraUse2Def;
	/** map from a def to use for return-passing induced DDs*/
	private Map<Integer, List<Integer>> retDef2Use;
	private Map<Integer, List<Integer>> retUse2Def;
	
	/** this ctor is used for creating the instance from deserialization during post-processing phase */
	public StaticDDInfo() {
		init();
		this.reachableMethods = null;
	}
	/** this ctor is used for creating the instance by static analysis */
	public StaticDDInfo(boolean _debugOut) {
		this.debugOut = _debugOut;
		init();
		this.reachableMethods = new LinkedHashSet<SootMethod>(); 
		this.reachableMethods.addAll(ProgramFlowGraph.inst().getReachableAppMethods());
	}
	
	private void init() {
		this.paraDef2Use = new LinkedHashMap<Integer, List<Integer>>();
		this.paraUse2Def = new LinkedHashMap<Integer, List<Integer>>();
		this.retDef2Use = new LinkedHashMap<Integer, List<Integer>>();
		this.retUse2Def = new LinkedHashMap<Integer, List<Integer>>();
	}
	
	@Override public String toString() {
		return "[Static partialInterDDs] " + super.toString();
	}
	
	/** build the static DD info --- fill the internal data structures */
	public int computeDDInfo() {
		if (!(paraDef2Use.isEmpty() && paraUse2Def.isEmpty() && retDef2Use.isEmpty() && retUse2Def.isEmpty())) {
			// already done before
			return 0;
		}
		
		/** traverse all classes and methods to computer the DDs per method */
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
				/*
				if (!reachableMethods.contains(sMethod)) {
					// skip unreachable methods
					continue;
				}
				*/
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				
				String meId = sMethod.getSignature();
				// -- DEBUG
				if (debugOut) {
					System.out.println("\npartialInterDDs computation: now processing method " + meId + "...");
				}
				
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				CFGDefUses cfgDUs = (CFGDefUses)cfg;
				
				//try 
				{
					createParameterDDs(cfgDUs);
					createReturnDDs(cfgDUs);
				}
				/* DEBUG
				catch (Throwable t) {
					
					System.err.println("failure occurred in creating interDD links for " + cfgDUs.getMethod());
					throw t;
				}
				*/
			}
		}
		
		return 0;
	} // computeDDInfo
	
	/** helper: add parameter def-use pair to the internal maps */
	protected void addParameterDefUse(Variable dv, Variable uv) {
		Integer did = EventInstrumenter.getVariableId(dv);
		Integer uid = EventInstrumenter.getVariableId(uv);
		assert did != null && uid != null;
		
		List<Integer> uses = paraDef2Use.get(did);
		if (null == uses) {
			uses = new ArrayList<Integer>();
			paraDef2Use.put(did, uses);
		}
		if (!uses.contains(uid)) {
			uses.add(uid);
		}
		
		List<Integer> defs = paraUse2Def.get(uid);
		if (null == defs) {
			defs = new ArrayList<Integer>();
			paraUse2Def.put(uid, defs);
		}
		if (!defs.contains(did)) {
			defs.add(did);
		}
	}
	/** helper: add return def-use pair to the internal maps */
	protected void addReturnDefUse(Variable dv, Variable uv) {
		Integer did = EventInstrumenter.getVariableId(dv);
		Integer uid = EventInstrumenter.getVariableId(uv);
		assert did != null && uid != null;
		
		List<Integer> uses = retDef2Use.get(did);
		if (null == uses) {
			uses = new ArrayList<Integer>();
			retDef2Use.put(did, uses);
		}
		if (!uses.contains(uid)) {
			uses.add(uid);
		}
		
		List<Integer> defs = retUse2Def.get(uid);
		if (null == defs) {
			defs = new ArrayList<Integer>();
			retUse2Def.put(uid, defs);
		}
		if (!defs.contains(did)) {
			defs.add(did);
		}
	}
	
	/** link actual (as def) to formal (as use) parameters */
	private void createParameterDDs(CFG cfg) {
		List<CallSite> cses = cfg.getCallerSites();
		for (CallSite cs : cses) {
			int naParams = cs.getNumActualParams();
			InvokeExpr iex = cs.getLoc().getStmt().getInvokeExpr();
			int startArgIdx = 0;
			if (iex instanceof InstanceInvokeExpr /*&& cs.isInstanceCall()*/) {
				startArgIdx = 1;
			}
			if (naParams < 1+startArgIdx || cfg.getMethod().getParameterCount() < 1) {
				// skip call sites with empty parameter list
				continue;
			}
			/* if there are multiple callees on the call site, we need link from the actual parameters
			 * to the formal parameters of each callee, conservatively for safety
			 */
			List<SootMethod> appCallees = cs.getAppCallees();
			for (SootMethod ce : appCallees) {
				if (!ce.equals(cfg.getMethod())) {
					// connect the caller to the right callee
					continue;
				}
				ReachableUsesDefs rudce = (ReachableUsesDefs) ProgramFlowGraph.inst().getCFG(ce);
				int nfParams = rudce.getNumFormalParams();
				assert naParams == nfParams;

				/*  per actual-formal parameter pair, the first pair connecting an object to the 'this' pointer for
				 *  instance-calls should be ignored
				 */
				int i = 0;
				for(i=startArgIdx; i<nfParams; i++) {
					//Stmt sIdFormal = rudce.getFormalParam(i).getIdStmt();
					Value aval = cs.getActualParam(i);
					Variable avar = null;
					if (aval instanceof Constant) {
						avar = new CSArgVar(aval, cs, i);
						EventInstrumenter.addConstantVariableToGlobalIndex(avar, cs.getLoc().getStmt());
					}
					else {
						 avar = Utils.makeVariable(aval, cs.getLoc().getStmt()); //new StdVariable(aval);
					}
					/*
					Value fval = rudce.getFormalParam(i).getV();
					Variable fvar = Utils.makeVariable(fval, sIdFormal); //new StdVariable(fval);
					
					addParameterDefUse(avar, fvar);
					*/
				} // for each parameter
			} // for each app callee
		} // for each call site
	} // createParameterDDs
	
	/** link returned value (as def) to the use of that return (as use) */
	private void createReturnDDs(CFG cfg) {
		SootMethod m = cfg.getMethod();
		if (m.getReturnType() instanceof VoidType) {
			/* skip if this method has merely a "void" return */
			return;
		}
		List<CallSite> callerSites = cfg.getCallerSites();
		for (CallSite caller : callerSites) {
			Stmt sCaller = caller.getLoc().getStmt();
			InvokeExpr iex = sCaller.getInvokeExpr();
			if (iex.getType().equals(VoidType.v())) {
				/* nothing is returned */
				continue;
			}
			assert !(sCaller instanceof ReturnStmt);
			if (!(sCaller instanceof AssignStmt)) {
				/* return value is not taken */
				continue;
			}

			/* returned variable whose value is used in the caller site */ 
			//Variable csretVar = Utils.makeVariable( ((AssignStmt)sCaller).getLeftOp(), sCaller );
			
			/* we need link each possible return in this method to the caller site */
			List<CFGNode> cfgnodes = cfg.getNodes(); //	cfg.getFirstRealNonIdNode().getSuccs();
			for (CFGNode _node : cfgnodes) {
				Stmt s = _node.getStmt();
				if (!(s instanceof ReturnStmt)) {
					/* just capture every return statement */
					continue;
				}
				
				Value retv = ((ReturnStmt)s).getOp();
				Variable rVar = null;
				if (retv instanceof Constant) {
					rVar = new ReturnVar(retv, _node);
					EventInstrumenter.addConstantVariableToGlobalIndex(rVar, s);
				}
				else {
					 rVar = Utils.makeVariable(retv, s); //new StdVariable(retv);
				}
				
				//addReturnDefUse(rVar, csretVar);
			} // for each CFG node in the callee, namely the method under visit
		} // for each caller site of the method under visit
	} // createReturnDDs
	
	/** accessories */
	// check DU pairing between the two given variable ids
	public boolean dupair(Integer id1, Integer id2) {
		if (paraDef2Use.containsKey(id1) && paraDef2Use.get(id1).contains(id2)) return true;
		if (paraUse2Def.containsKey(id1) && paraUse2Def.get(id1).contains(id2)) return true;
		
		if (retDef2Use.containsKey(id1) && retDef2Use.get(id1).contains(id2)) return true;
		if (retUse2Def.containsKey(id1) && retUse2Def.get(id1).contains(id2)) return true;
		
		return false;
	}
	
	// retrieve the ids of variables having return or parameter passing induced DD with the given variable
	public List<Integer> getPairedDefs(Integer id) {
		if (paraUse2Def.containsKey(id)) return paraUse2Def.get(id);
		if (retUse2Def.containsKey(id)) return retUse2Def.get(id);
		
		return null;
	}
	public List<Integer> getPairedUses(Integer id) {
		if (paraDef2Use.containsKey(id)) return paraDef2Use.get(id);
		if (retDef2Use.containsKey(id)) return retDef2Use.get(id);
		
		return null;
	}
	
	/** check if the variable id is on a return or call site statement */
	public boolean isOnReturn(Integer id) {
		return retDef2Use.containsKey(id);
	}
	public boolean isOnCall(Integer id) {
		return paraDef2Use.containsKey(id);
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	///////////////////////////////////////////////////////////////////////////////////////////////////
	private static final long serialVersionUID = 0x458211DE;
	
    /** Save the state of the <tt>StaticDDInfo</tt> instance to a stream (i.e., serialize it) */
    private void writeObject(java.io.ObjectOutputStream s)  throws IOException
    {
        // Write out any hidden stuff
        s.defaultWriteObject();

        // the real contents to be serialized
        s.writeObject(this.paraDef2Use);
        s.writeObject(this.paraUse2Def);
        s.writeObject(this.retDef2Use);
        s.writeObject(this.retUse2Def);
        
        s.flush();
    }

    /** Load the state of the <tt>StaticDDInfo</tt> instance from a stream (i.e., deserialize it) */
    @SuppressWarnings("unchecked")
	private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException
    {
        // Read any hidden stuff
        s.defaultReadObject();
        
        // Load the real contents
        this.paraDef2Use = (Map<Integer, List<Integer>>) s.readObject();
        this.paraUse2Def = (Map<Integer, List<Integer>>) s.readObject();
        this.retDef2Use = (Map<Integer, List<Integer>>) s.readObject();
        this.retUse2Def = (Map<Integer, List<Integer>>) s.readObject();
        // -
    }
    
    /** serailize the instance of this to a given external file */ 
	public int SerializeToFile(String fnTarget) {
		/* serialize for later deserialization in the post-processing phase */
		if ( fnTarget.isEmpty() ) {
			return -1;
		}
		
		computeDDInfo();
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
	} // SerializeToFile
	
    /** instantiate an object of this by reading an external file */
	public int DeserializeFromFile(String fnSource) {
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
			
			StaticDDInfo readObject = (StaticDDInfo) ois.readObject();
			this.paraDef2Use.clear();
			this.paraDef2Use.putAll(readObject.paraDef2Use);
			
			this.paraUse2Def.clear();
			this.paraUse2Def.putAll(readObject.paraUse2Def);
			
			this.retDef2Use.clear();
			this.retDef2Use.putAll(readObject.retDef2Use);
			
			this.retUse2Def.clear();
			this.retUse2Def.putAll(readObject.retUse2Def);
			
			ois.close();
			bis.close();
			// --
		}
		catch (FileNotFoundException e) { 
			System.err.println("Failed to locate the given input file " + fnSource);
			return -1;
		}
		catch (ClassCastException e) {
			System.err.println("Failed to cast the object deserialized to StaticDDInfo!");
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
	public int dumpDDMappings(PrintStream os) {
		computeDDInfo();
		
		os.println("[parameter def->use mapping]");
		for (Map.Entry<Integer, List<Integer>> en : this.paraDef2Use.entrySet()) {
			os.println(en.getKey() + " -> " + en.getValue());	
		}
		os.println();
		
		os.println("[parameter use->def mapping]");
		for (Map.Entry<Integer, List<Integer>> en : this.paraDef2Use.entrySet()) {
			os.println(en.getKey() + " <- " + en.getValue());	
		}
		os.println();
		
		os.println("[return def->use mapping]");
		for (Map.Entry<Integer, List<Integer>> en : this.retDef2Use.entrySet()) {
			os.println(en.getKey() + " -> " + en.getValue());	
		}
		os.println();
		
		os.println("[return use->def mapping]");
		for (Map.Entry<Integer, List<Integer>> en : this.retDef2Use.entrySet()) {
			os.println(en.getKey() + " <- " + en.getValue());	
		}
		os.println();
		
		return 0;
	} // dumpDDMappings
	
} // definition of StaticDDInfo

/* vim :set ts=4 tw=4 tws=4 */
