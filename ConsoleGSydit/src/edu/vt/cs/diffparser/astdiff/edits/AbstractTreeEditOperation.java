package edu.vt.cs.diffparser.astdiff.edits;

import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.tree.JavaStructureNode;

public abstract class AbstractTreeEditOperation<T> implements ITreeEditOperation<T> {

	private static final long serialVersionUID = -685682530591380278L;

	protected GeneralNode parentNode = null;
	
	protected T cur;
	
	protected CONTENT_TYPE ct;
	
	protected int position;
	
	public CONTENT_TYPE getContentType() {
		return ct;
	}
	
	public GeneralNode getParentNode() {
		return parentNode;
	}
	
	public void setParentNode(GeneralNode n) {
		parentNode = n;
	}
	
	public void setContentType(CONTENT_TYPE ct) {
		this.ct = ct;
	}
	
	public void setPosition(int p) {
		position = p;
	}
	
	public T getCurrent() {
		return cur;
	}
	
	public int getPosition() {
		return position;
	}
}
