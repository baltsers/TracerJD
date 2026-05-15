/**
 * File: src/com/VariableInfo.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 02/17/14		hcai		created, encapsulating all per-variable information to be traced
 * 05/12/14		hcai		added DUA pairing props
 * 05/13/14		hcai		tested/fixed duapair()
 * 06/16/14		hcai		fixed duapair again: in def-use pairing, locals are matched by variable id; 
 * 								heap objects are matched via base id and, if applicable, array indexes
 * 07/11/14		hcai		added time-stamp to the runtime tracing record for a variable: variables on a same statement may not share
 * 							the time-stamp of the statement --- e.g., uses have smaller time-stamps than definitions on a call site 
 * 07/24/14		hcai		in duapair: match field name and base address for fieldRef variable def-use pairing
*/
package com;

import java.io.IOException;
import java.io.Serializable;

/** describe a complete set of information that needs be traced for a variable */
public class VariableInfo implements Serializable, Comparable<VariableInfo> {
	protected Integer vid; // variable index
	protected String vname; // string representation of the variable---specific prefix: &CP for callsite parameter; &RT for ret-val.
	protected String vvalue; // runtime value of the variable 
	protected Integer baseid; // [optional] object id of the base object for a heap variable
	protected String aridx; // [optional] array element index for an array reference variable
	protected Long ts; // the time-stamp at the execution of a probe for this variable

	protected void reset() {
		vid = 0;
		vname = "";
		vvalue = "";
		baseid = 0;
		aridx = "";
		ts = 0L;
	}

	public VariableInfo() {
		reset();
	}

	public VariableInfo(int _vid, String _vname) {
		reset();
		this.vid = _vid;
		this.vname = _vname;
	}

	public VariableInfo(int _vid, String _vname, String _vvalue) {
		reset();
		//this (_vid, _vname);
		this.vid = _vid;
		this.vname = _vname;
		this.vvalue = _vvalue;
	}
	
	@Override public boolean equals(Object _v) {
		VariableInfo v = (VariableInfo)_v;
		return 	v.vid.intValue()==vid.intValue() && 
				v.vname.compareTo(vname)==0 && 
				v.baseid.intValue()==baseid.intValue() && 
				v.aridx.compareTo(aridx)==0 && 
				v.ts.longValue()==ts.longValue();
	}
	
	/** if this object forms a DUA pair with the given object */
	public boolean dupair(Object _v) {
		VariableInfo v = (VariableInfo)_v;
		//if (Math.abs(v.vid)!=Math.abs(vid)) return false;
		/*
		if (Math.abs(v.vid)==Math.abs(vid)) return true;
		else if (baseid==0 && aridx.length()<1) return false;
		*/
		// for locals, match by variable ids
		if (baseid==0 && aridx.length()<1) {
			return Math.abs(v.vid)==Math.abs(vid); 
		}
		// for heap objects, match by (runtime) object addresses 
		/**if (baseid != 0 && v.baseid.intValue()!=baseid.intValue()) return false;*/
		if (baseid != 0 && aridx.length()<1) {
			if (v.baseid.intValue()!=baseid.intValue()) return false;
			String a = this.vname;
			if (a.contains("&")) a = a.substring(0, a.indexOf('&'));
			String b = v.vname;
			if (b.contains("&")) b = b.substring(0, b.indexOf('&'));
			return a.compareTo(b)==0;
		}
		// for array element in particular, match in addition by array indexes
		/**if (aridx.length()>=1 && v.aridx.compareTo(aridx)!=0) return false;*/
		if (baseid != 0 && aridx.length()>=1) {
			if (v.baseid.intValue()!=baseid.intValue()) return false;
			return v.aridx.compareTo(aridx)==0;
		}
		assert false; // cannot get here!
		return true;
	}

	public void setBaseId(int _baseid) { this.baseid = _baseid; }
	public void setAridx(String _aridx) { this.aridx = _aridx; }
	public void setTS(long _ts) { this.ts = _ts; }
	
	public int getVarId() { return this.vid; }
	public String getVarname() { return this.vname; }
	public String getVarValue() { return this.vvalue; }
	public int getBaseId() { return this.baseid; }
	public String getAridx() { return this.aridx; }
	public long getTS() { return this.ts; }
	
	public String toString() {
		String ostr = "varid=" + vid + ",vname=" + vname; 
		if (vvalue.length()>0) { ostr = ostr + ",vvalue=" + vvalue; }
		if (0 != baseid) { ostr = ostr + ",baseid=" + baseid; }
		if (aridx.length()>0) { ostr = ostr + ",aridx=" + aridx; }
		ostr = ostr + ",ts=" + ts;
		return ostr;
	}
	
	@Override public int compareTo(VariableInfo o) {
		return this.ts.compareTo(o.ts);
	}

	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	///                                           SERIALIZATION AND DESERIALIZATION
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	private static final long serialVersionUID = 0x4382FFDE;
	private void writeObject(java.io.ObjectOutputStream s)
    throws IOException {
		// Write out any hidden stuff
		s.defaultWriteObject();
	}
	
	private void readObject(java.io.ObjectInputStream s)
    throws IOException, ClassNotFoundException {
		// Read any hidden stuff
		s.defaultReadObject();
	}
}

/* vim :set ts=4 tw=4 tws=4 */
