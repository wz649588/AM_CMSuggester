package edu.vt.cs.prediction.neo;

import java.util.ArrayList;
import java.util.Deque;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.swing.tree.DefaultMutableTreeNode;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.BreakStatement;
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

import ch.uzh.ifi.seal.changedistiller.treedifferencing.Node;
import edu.vt.cs.append.JavaExpressionConverter;

/**
 * 
 * @author Ye Wang
 * @since 07/09/2017
 *
 */
public class LeafStatementFinder extends ASTVisitor {

	private ASTNode root;
	
	private List<ASTNode> leaves = new ArrayList<>();
	
//	private Map<ASTNode, String> nodeToString = new HashMap<>();
	
	private DefaultMutableTreeNode treeRoot;
	
	private Deque<DefaultMutableTreeNode> stack;
	
	public LeafStatementFinder(ASTNode root) {
		this.root = root;
		stack = new LinkedList<>();
		treeRoot = new DefaultMutableTreeNode();
		stack.push(treeRoot);
	}
	
	private void push(ASTNode node) {
		DefaultMutableTreeNode treeNode = new DefaultMutableTreeNode(node);
		push(treeNode);
	}
	
	private void push(DefaultMutableTreeNode node) {
		getCurrentParent().add(node);
		stack.push(node);
	}
	
	private void pop() {
		stack.pop();
	}
	
	private DefaultMutableTreeNode getCurrentParent() {
		return stack.peek();
	}
	
//	private String generateCodeString(ASTNode node) {
//		JavaExpressionConverter converter = new JavaExpressionConverter();
//		node.accept(converter);
//		Node root = converter.getRoot();
//		Enumeration<Node> traversal = root.preorderEnumeration();
//		StringBuilder builder = new StringBuilder();
//		while (traversal.hasMoreElements()) {
//			Node n = traversal.nextElement();
//			if (n.isLeaf()) {
//				builder.append(n.getValue());
//			}
//		}
//		return builder.toString();
//	}
	
	
	@Override
	public void preVisit(ASTNode node) {
		if (node instanceof Statement)
			push(node);
	}
	
	@Override
	public void postVisit(ASTNode node) {
		if (node instanceof Statement)
			pop();
	}
	
	private void extractLeaves() {
		Enumeration<DefaultMutableTreeNode> traversal = treeRoot.preorderEnumeration();
		while (traversal.hasMoreElements()) {
			DefaultMutableTreeNode node = traversal.nextElement();
			if (!node.isRoot() && node.isLeaf()) {
				leaves.add((ASTNode) node.getUserObject());
			}
		}
	}
	
	public List<ASTNode> getLeaves() {
		return leaves;
	}
	
	public void execute() {
		root.accept(this);
		extractLeaves();
//		for (ASTNode node: leaves) {
//			String codeString = generateCodeString(node);
//			nodeToString.put(node, codeString);
//		}
	}
	
}
