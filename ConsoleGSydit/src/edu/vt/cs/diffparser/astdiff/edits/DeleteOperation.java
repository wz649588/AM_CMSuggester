package edu.vt.cs.diffparser.astdiff.edits;

public class DeleteOperation<T> extends AbstractTreeEditOperation<T> {

	private static final long serialVersionUID = 2874374375649525369L;

	public DeleteOperation(T cur) {
		this.cur = cur;
	}
	
	public DeleteOperation(T cur, CONTENT_TYPE ct) {
		this(cur);
		this.ct = ct;
	}
	
	@Override
	public EDIT getOperationType() {
		return EDIT.DELETE;
	}
	
	@Override
	public String toString() {
		return "Delete(" + ct + "): " + cur + " under " + parentNode; 
	}
}
