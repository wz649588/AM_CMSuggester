package edu.vt.cs.diffparser.util;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;

public class ASTMethodFinder extends ASTVisitor{

	private boolean visitInnerMethod;
	private MethodDeclaration node;
	private SourceCodeRange range;
	
	@Override
	public boolean visit(MethodDeclaration node) {
		if (this.node == null && !visitInnerMethod 
				&& node.getStartPosition() == range.startPosition 
				&& node.getLength() == range.length) {
			this.node = node;
		} else if (this.node == null && visitInnerMethod 
				&& node.getParent() instanceof AnonymousClassDeclaration
				&& node.getStartPosition() == range.startPosition
				&& node.getLength() == range.length) {
			this.node = node;
		}
		return visitInnerMethod;
	}
	
	public MethodDeclaration lookForMethod(CompilationUnit cu, SourceCodeRange scr) {
		this.visitInnerMethod = false;
		this.node = null;
		this.range = scr;
		cu.accept(this);
		if (this.node == null) {
			this.visitInnerMethod = true;
			cu.accept(this);
		}
		return this.node;
	}
}
