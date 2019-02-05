package edu.vt.cs.treebuilders;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Stack;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.ContinueStatement;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.LabeledStatement;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.SynchronizedStatement;
import org.eclipse.jdt.core.dom.ThrowStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

import edu.vt.cs.diffparser.tree.JavaAnonymousClassNode;
import edu.vt.cs.diffparser.tree.JavaImplementationNode;
import edu.vt.cs.diffparser.tree.JavaMethodHeaderNode;
import edu.vt.cs.diffparser.tree.JavaStatementNode;
import edu.vt.cs.diffparser.util.ASTAnonymousClassDeclarationFinder;
import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaMethodTreeBuilder extends AbstractTreeBuilder<JavaImplementationNode>{
	
	private MethodDeclaration md = null;
	
	private ASTAnonymousClassDeclarationFinder acdFinder;
	
	public static final String ANONY_ANCHOR = "anony_anchor"; 
	
	public JavaMethodTreeBuilder() {
		acdFinder = new ASTAnonymousClassDeclarationFinder();
	}
	
	public void init(MethodDeclaration md) {
		fNodeStack = new Stack<JavaImplementationNode>();
		this.md = md;
		this.cur = null;
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {
		JavaMethodHeaderNode n = null;
		if (!fNodeStack.isEmpty()) {
			n = new JavaMethodHeaderNode(node.getNodeType(), 
					node.getName().getIdentifier(), 
					new SourceCodeRange(node.getStartPosition(), node.getLength()),
					node.parameters());
			push(n);
		} else {
			n = new JavaMethodHeaderNode(node.getNodeType(), 
					node.getName().getIdentifier(), 
					new SourceCodeRange(node.getStartPosition(), node.getLength()),
					node.parameters());
			n.setMethodDeclaration(node);
			this.root = n;
			fNodeStack.push(root);
			cur = root;
		}
		return true;
	}
	
	@Override
	public void endVisit(MethodDeclaration node) {
		pop();
	}
	
	@Override
	public boolean visit(AnonymousClassDeclaration node) {
		JavaAnonymousClassNode n = new JavaAnonymousClassNode(node.getNodeType(), "anonyClass", 
				new SourceCodeRange(node.getStartPosition(), node.getLength()));
		push(n);
		return true;
	}
	
	@Override
	public void endVisit(AnonymousClassDeclaration node){
		pop();
	}

	@Override
	public boolean visit(AssertStatement node) {
		push("assert", node, node.getExpression(), node.getMessage());
		return false;		
	}
	
	@Override
	public void endVisit(AssertStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(BreakStatement node) {
		push("break", node, node.getLabel());
		return false;
	}

	@Override
	public void endVisit(BreakStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(CatchClause node) {
		push("catch", node, node.getException());
		node.getBody().accept(this);
		return false;
	}

	@Override
	public void endVisit(CatchClause node) {
		pop();
	}
	
	@Override
	public boolean visit(ConstructorInvocation node) {
		push("this()", node, node);
		return true;
	}
	
	@Override
	public void endVisit(ConstructorInvocation node) {
		pop();
	}
	
	@Override
	public boolean visit(ContinueStatement node) {
		push("continue", node, node.getLabel());
		return false;
	}

	@Override
	public void endVisit(ContinueStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(DoStatement node) {
		push("do-while", node, node.getExpression());
		return true;
	}

	@Override
	public void endVisit(DoStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(EnhancedForStatement node) {
		push("en-for", node, node.getParameter(), node.getExpression());
		return true;
	}

	@Override
	public void endVisit(EnhancedForStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(ExpressionStatement node) {
		return pushExpressionNode("expr", node);		
	}

	@Override
	public void endVisit(ExpressionStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(ForStatement node) {
		List<ASTNode> expressions = new ArrayList<ASTNode>();
		expressions.addAll(node.initializers());
		expressions.add(node.getExpression());
		expressions.addAll(node.updaters());
		push("for", node, expressions);
		return true;
	}
	
	@Override
	public void endVisit(ForStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(IfStatement node) {
		push("if", node, node.getExpression());

		if (node.getThenStatement() != null) {
			Statement thenStmt = node.getThenStatement();
			// the node's type should be BLOCK
			push("then", thenStmt);
			thenStmt.accept(this);
			pop();
		}

		if (node.getElseStatement() != null) {
			Statement elseStmt = node.getElseStatement();
			push("else", elseStmt);
			elseStmt.accept(this);
			pop();
		}
		return false;
	}

	@Override
	public void endVisit(IfStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(LabeledStatement node) {
		push("label", node, node.getLabel());
		node.getBody().accept(this);
		return false;
	}

	@Override
	public void endVisit(LabeledStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(ReturnStatement node) {
		push("return", node, node.getExpression());
		return true;
	}
	
	@Override
	public void endVisit(ReturnStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(SuperConstructorInvocation node) {
		push("super()", node, node);
		return true;
	}

	@Override
	public void endVisit(SuperConstructorInvocation node) {
		pop();
	}
	
	@Override
	public boolean visit(SwitchCase node) {
		if (node.isDefault()) {
			push("default", node, node.getExpression());
		} else {
			push("case", node, node.getExpression());
		}
		return false;
	}
	
	@Override
	public void endVisit(SwitchCase node) {
		pop();
	}
	
	@Override
	public boolean visit(SwitchStatement node) {
		push("switch", node, node.getExpression());
		visitList(node.statements());
		return false;
		// return true;
	}

	@Override
	public void endVisit(SwitchStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(SynchronizedStatement node) {
		push("sync", node, node.getExpression());
		return true;
	}

	@Override
	public void endVisit(SynchronizedStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(ThrowStatement node) {
		push("throw", node, node.getExpression());
		return false;
	}

	@Override
	public void endVisit(ThrowStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(TryStatement node) {
		push("try", node, Collections.EMPTY_LIST); // push the outside "try" node

		push("try-body", node.getBody(), Collections.EMPTY_LIST);
		node.getBody().accept(this);
		pop();

		visitList(node.catchClauses());
		if (node.getFinally() != null) {
			ASTNode fNode = node.getFinally();
			push("finally", fNode, Collections.EMPTY_LIST);
			fNode.accept(this);
			pop();
		}
		return false;
	}

	@Override
	public void endVisit(TryStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(VariableDeclarationStatement node) {
		return pushExpressionNode("decl", node);
	}

	@Override
	public void endVisit(VariableDeclarationStatement node) {
		pop();
	}
	
	@Override
	public boolean visit(WhileStatement node) {
		push("while", node, node.getExpression());
		return true;
	}

	@Override
	public void endVisit(WhileStatement node) {
		pop();
	}
	
	
	private void push(String defaultStrValue, ASTNode node, ASTNode... expressions) {
		JavaStatementNode n = new JavaStatementNode(node.getNodeType(), 
				defaultStrValue, 
				new SourceCodeRange(node.getStartPosition(), node.getLength()),
				expressions);
		push(n);
	}
	
	private boolean pushExpressionNode(String defaultStrValue, Statement node) {
		List<ASTNode> tmpNodes = acdFinder.findACD(node);
		if (tmpNodes == null) {
			push (defaultStrValue, node, 
					node instanceof ExpressionStatement?
							((ExpressionStatement)node).getExpression()
						:	node);//VariableDeclarationStatement
			return false;
		}
		String nodeStr = node.toString();
		ASTNode tmpNode = null;
		String[] segs = null;
		String tmpStr = null;
		for (int i = 0; i < tmpNodes.size(); i++) {
			tmpNode = tmpNodes.get(i);
			tmpStr = tmpNode.toString();
			if (nodeStr.contains(tmpStr)) {
				segs = nodeStr.split(tmpNode.toString());
				nodeStr = segs[0] + ANONY_ANCHOR + "_" + i + segs[1];			
			}			
		}
		push(defaultStrValue + ":" + nodeStr, node);
		return true;
	}
	
	private void push(String defaultValue, ASTNode node, List<ASTNode> astNodeList) { 
		push(defaultValue, node, astNodeList.toArray(new ASTNode[astNodeList.size()]));
	}
	
	private void push(JavaImplementationNode n){
		cur.add(n);
		cur = n;
		fNodeStack.push(cur);
	}
	
	private void pop() {
		fNodeStack.pop();
		if(!fNodeStack.isEmpty())
			cur = fNodeStack.peek();
		else 
			cur = null;
	}
	
	private void visitList(List<ASTNode> list) {
		for (ASTNode element : list) {
			element.accept(this);
		}
	}
}
