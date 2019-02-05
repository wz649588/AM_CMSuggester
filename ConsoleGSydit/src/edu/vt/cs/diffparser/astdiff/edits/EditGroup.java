package edu.vt.cs.diffparser.astdiff.edits;

import java.util.ArrayList;
import java.util.List;

public class EditGroup<T> implements ITreeEditOperation<T> {
	private static final long serialVersionUID = -7842381198712024217L;
	
	protected List<ITreeEditOperation<T>> edits;
	
	protected CONTENT_TYPE ct;
	
	protected String strValue;
	
	public EditGroup(CONTENT_TYPE type) {
		ct = type;
		edits = new ArrayList<ITreeEditOperation<T>>();
	}
	
	@Override
	public EDIT getOperationType() {
		return EDIT.EDIT_GROUP;
	}
	
	public void add(ITreeEditOperation<T> edit) {
		edits.add(edit);
	}
	
	public boolean isEmpty() {
		return edits.isEmpty();
	}
	
	public void setStrValue(String str) {
		strValue = str;
	}

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer("EditGroup(" + ct + "):");
		if (strValue != null) {
			buf.append(strValue);
		}
		buf.append("\n");
		for (ITreeEditOperation<T> edit : edits) {
			buf.append("\t").append(edit).append("\n");
		}
		return buf.toString();
	}

	@Override
	public CONTENT_TYPE getContentType() {
		return ct;
	}	
}
