package edu.vt.cs.diffparser.astdiff.edits;

public class LowlevelEditscript extends Editscript {

	private String strValue;
	
	public LowlevelEditscript(String str) {
		strValue = str;
	}
	
	public String getStrValue() {
		return strValue;
	}
	
	public void setStrValue(String str) {
		strValue = str;
	}
	
	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer("script:----------" + strValue + "\n");
		for (ITreeEditOperation edit : edits) {
			buf.append(edit).append("\n");
		}
		return buf.toString();
	}
}
