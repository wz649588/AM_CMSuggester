package edu.vt.cs.diffparser.astdiff.edits;

public abstract class StringDeclarationOperation implements ITreeEditOperation<String> {

	private static final long serialVersionUID = 1080267169406727540L;

	protected int nodeType;
	
	protected String strValue;

	public int getNodeType() {
		return nodeType;
	}
	
	public void setNodeType(int type) {
		nodeType = type;
	}

	public String getStrValue() {
		return strValue;
	}

	public void setStrValue(String strValue) {
		this.strValue = strValue;
	}
}
