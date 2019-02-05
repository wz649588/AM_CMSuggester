package edu.vt.cs.diffparser.astdiff.edits;

public class UpdateOperation<T> extends AbstractTreeEditOperation<T> {	
	private static final long serialVersionUID = -2880438745683432230L;
	
	protected T newCur;

	public UpdateOperation(T cur, T newCur) {
		this.cur = cur;
		this.newCur = newCur;
	}
	
	public UpdateOperation(T cur, T newCur, CONTENT_TYPE ct) {
		this(cur, newCur);
		this.ct = ct;
	}
	
	@Override
	public EDIT getOperationType() {
		return EDIT.UPDATE;
	}
	
	public T getNewCurrent() {
		return newCur;
	}
	
	@Override
	public String toString() {
		return "Update(" + ct + "): " + cur + "to "+ newCur + " under " + parentNode; 
	}
}
