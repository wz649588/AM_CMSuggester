package edu.vt.cs.diffparser.astdiff.edits;

import edu.vt.cs.diffparser.tree.JavaStructureNode;

public class MoveOperation<T> extends AbstractTreeEditOperation<T> {
	private static final long serialVersionUID = 2037943470459334071L;
	
	protected JavaStructureNode newParent;

	@Override
	public EDIT getOperationType() {
		return EDIT.MOVE;
	}

	public JavaStructureNode getNewParentNode() {
		return newParent;
	}
}
