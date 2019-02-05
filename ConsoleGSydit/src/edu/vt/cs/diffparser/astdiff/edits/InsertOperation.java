package edu.vt.cs.diffparser.astdiff.edits;

public class InsertOperation<T> extends AbstractTreeEditOperation<T>{

	private static final long serialVersionUID = 6625482866768063818L;

	public InsertOperation(T cur) {
		this.cur = cur;
	}
	
	public InsertOperation(T cur, CONTENT_TYPE ct) {
		this(cur);
		this.ct = ct;
	}
	
	@Override
	public EDIT getOperationType() {
		return EDIT.INSERT;
	}
	
	@Override
	public String toString() {
		return "Insert(" + ct + "): " + cur + " under " + parentNode; 
	}
}
