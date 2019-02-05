package edu.vt.cs.prediction.neo;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.ContinueStatement;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.EmptyStatement;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.LabeledStatement;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.SynchronizedStatement;
import org.eclipse.jdt.core.dom.ThrowStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.TypeDeclarationStatement;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class StatementVisitor extends ASTVisitor {

	private Statement node;
	private SourceCodeRange range;
	
	@Override
	public boolean visit(AssertStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(Block n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(BreakStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ConstructorInvocation n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ContinueStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(DoStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(EmptyStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(EnhancedForStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ExpressionStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ForStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(IfStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(LabeledStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ReturnStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(SuperConstructorInvocation n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(SwitchCase n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(SwitchStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(SynchronizedStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(ThrowStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(TryStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(TypeDeclarationStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(VariableDeclarationStatement n) {
		return pVisit(n);
	}
	
	@Override
	public boolean visit(WhileStatement n) {
		return pVisit(n);
	}
	
	private boolean pVisit(Statement n) {
		if (node == null
				&& range.startPosition == n.getStartPosition()
				&& range.length == n.getLength()) {
			node = n;
		}
		return true;
	}
	
	public Statement lookForNode(ASTNode root, SourceCodeRange scr) {
		node = null;
		range = scr;
		root.accept(this);
		return node;
	}
}
