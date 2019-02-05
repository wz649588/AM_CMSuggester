package edu.vt.cs.treebuilders;

import java.util.Stack;

import org.eclipse.jdt.core.dom.ASTVisitor;

public abstract class AbstractTreeBuilder<T> extends ASTVisitor{

	protected Stack<T> fNodeStack;
	protected T cur;
	protected T root;
	public T getRoot() {
		return root;
	}

}
