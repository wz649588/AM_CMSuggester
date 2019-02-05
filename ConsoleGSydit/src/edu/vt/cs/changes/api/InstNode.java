package edu.vt.cs.changes.api;

public class InstNode extends SNode{
	private int iType = 0;
	private int instIndex = 0;
	
	public InstNode(String s, int id, int iType, int instIndex) {
		super(s, SNode.INST_NODE, id);
		this.iType = iType;
		this.instIndex = instIndex;
	}

	public int getInstIndex() {
		return instIndex;
	}
	
	public int getInstType() {
		return iType;
	}
	
	@Override
	public String toString() {
		return toTypeString(iType) + " " + label;
	}
	
	public String toTypeString(int iType) {
		return InstType.toTypeString(iType);
	}

}
