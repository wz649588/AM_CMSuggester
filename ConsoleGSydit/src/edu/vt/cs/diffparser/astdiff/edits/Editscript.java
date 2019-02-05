package edu.vt.cs.diffparser.astdiff.edits;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.CONTENT_TYPE;
import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.EDIT;

public class Editscript {

	protected LinkedList<ITreeEditOperation> edits;	
	
	public Editscript() {
		edits = new LinkedList<ITreeEditOperation>();		
	}
	
	public void add(ITreeEditOperation edit) {
		edits.add(edit);
	}
	
	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer("script:----------\n");
		for (ITreeEditOperation edit : edits) {
			buf.append(edit).append("\n");
		}
		return buf.toString();
	}
}
