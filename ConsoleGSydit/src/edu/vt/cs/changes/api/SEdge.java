package edu.vt.cs.changes.api;

public class SEdge {

	public int insn;
	public int idxOfUse;
	public boolean mark;
	
	public SEdge(int insn, int idxOfUse) {
		this.insn = insn;
		this.idxOfUse = idxOfUse;
		this.mark = false;
	}
	
	public void enableMark() {
		this.mark = true;
	}
}
