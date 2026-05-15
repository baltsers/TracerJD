/**
 * File: src/com/StaticOptions.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/15/14		hcai		created; command-line argument processing of static analysis options
 * 03/21/14		hcai		added option for value tracing black lists;
 * 03/28/14		hcai		added option for static CD info computation
 * 06/12/14		hcai		added option for toggling (all or used only) value tracing 
 * 08/07/14		hcai		changed the default of 'sclinit' to true to avoid losing traces from the static initializer in the entry class,
 * 							which is executed before the entry method (such as 'main')
 * 08/16/14		hcai		added option for profiling statement execution cost only
*/
package com;

import java.util.ArrayList;
import java.util.List;

public class StaticOptions {
	protected boolean debugOut = false;
	protected boolean dumpJimple = false;
	/* for method entry/exit event monitoring: entry from static initializer or not (main method) */ 
	protected boolean sclinit = false;
	protected boolean wrapTryCatch = false;
	protected boolean dumpFunctionList = false;
	/* for exception profiling: if producing reports about uncaught exceptions or not (wrapTryCatch needs be set if this option is enabled) */
	protected boolean statUncaught = false;
	/* for dynamic alias monitoring expressly: cache until the end of execution or dump immediately */
	protected boolean cachingOIDs = false;
	/* the 'black list' of object types that value tracing instrumentation for defined variables should bypass */
	protected List<String> defblacktypes = new ArrayList<String>();
	/* the 'black list' of object types that value tracing instrumentation for used variables should bypass */
	protected List<String> useblacktypes = new ArrayList<String>();
	
	/* it is expensive thus optional to compute static CDs */
	protected boolean staticCDInfo = false;
	
	/** don't trace any used variable values */
	protected boolean notracingusedval = false;
	/** don't trace any variable values, including definitions */
	protected boolean notracingval = false;
	
	/** profile statement execution cost only */
	protected boolean stmtExecTimeProfiling = false;

	public boolean debugOut() { return debugOut; }
	public boolean dumpJimple() { return dumpJimple; }
	public boolean sclinit() { return sclinit; }
	public boolean wrapTryCatch() { return wrapTryCatch; }
	public boolean dumpFunctionList() { return dumpFunctionList; }
	public boolean statUncaught() { return statUncaught; }
	public boolean cachingOIDs() { return cachingOIDs; }
	public List<String> defblacktypes() { return defblacktypes; }
	public List<String> useblacktypes() { return useblacktypes; }
	public boolean notracingusedval() { return notracingusedval; }
	public boolean notracingval() { return notracingval; }
	public boolean staticCDInfo() { return staticCDInfo; }
	
	public boolean stmtExecTimeProfiling() { return stmtExecTimeProfiling; }
		
	public String[] process(String[] args) {
		List<String> argsFiltered = new ArrayList<String>();
		boolean allowPhantom = true;
		
		for (int i = 0; i < args.length; ++i) {
			String arg = args[i];

			if (arg.equals("-debug")) {
					debugOut = true;
			}
			else if (arg.equals("-dumpJimple")) {
				dumpJimple = true;
			}
			else if (arg.equals("-nclinit")) {
				sclinit = false;
			}
			else if (arg.equals("-wrapTryCatch")) {
				wrapTryCatch = true;
			}
			else if (arg.equals("-statUncaught")) {
				statUncaught = true;
			}
			else if (arg.equals("-dumpFunctionList")) {
				dumpFunctionList = true;
			}
			else if (arg.equals("-cachingOIDs")) {
				cachingOIDs = true;
			}
			else if (arg.equals("-nophantom")) {
				allowPhantom = false;
			}
			else if (arg.startsWith("-defblacktypes")) {
				defblacktypes = dua.util.Util.parseStringList(args[i+1], ',');
				i++;
			}
			else if (arg.startsWith("-useblacktypes")) {
				useblacktypes = dua.util.Util.parseStringList(args[i+1], ',');
				i++;
			}
			else if (arg.equals("-notracingusedval")) {
				notracingusedval = true;
			}
			else if (arg.equals("-notracingval")) {
				notracingval = true;
				notracingusedval = true;
			}
			else if (arg.startsWith("-staticCD")) {
				staticCDInfo = true;
			}
			else if (arg.startsWith("-stmtProf")) {
				stmtExecTimeProfiling = true;
			}
			else {
				argsFiltered.add(arg);
			}
		}
		
		if (allowPhantom) {
			argsFiltered.add("-allowphantom");
		}
		
		String[] arrArgsFilt = new String[argsFiltered.size()];
		return (String[]) argsFiltered.toArray(arrArgsFilt);
	}
}

/* vim :set ts=4 tw=4 tws=4 */

