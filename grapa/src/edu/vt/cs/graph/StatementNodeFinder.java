package edu.vt.cs.graph;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;

import com.ibm.wala.ipa.slicer.Statement;

public class StatementNodeFinder extends ASTVisitor{
	
	private boolean isMatched = false;
	private int startPos = 0;
	private int endPos = 0;
	private ASTNode coveredNode = null;
	private Statement stmt = null;
	private CompilationUnit cu = null;
	private int src_line_number = 0;
	
	public StatementNodeFinder(ASTNode cu, int src_line_number, Statement statement) {
		this.cu = (CompilationUnit)cu;
		this.src_line_number = src_line_number;
		cu.accept(this);
	}
	
	@Override
	public void preVisit(ASTNode node) {
		
	}
	
	@Override
	public boolean visit(FieldDeclaration node) {
		if (!isMatched) {
			int lineNum = cu.getLineNumber(node.getStartPosition());
			if (lineNum == src_line_number) {
				isMatched = true;
				coveredNode = node;
			}
		}		
		return false;
	}
	
//	public StatementNodeFinder(ASTNode cu, int startPos, int endPos, Statement statement) {
//		isMatched = false;
//		this.startPos = startPos;
//		this.endPos = endPos;
//		cu.accept(this);
//	}
	
	public ASTNode getCoveredNode() {
		return coveredNode;
	}
	
//	public ASTNode getEnclosingStatement(ASTNode node) {
//		ASTNode tmp = node;
//		while(tmp != null && !(tmp instanceof org.eclipse.jdt.core.dom.Statement)) {
//			tmp = tmp.getParent();
//		}
//		return tmp;
//	}
//	
//	@Override
//	public void preVisit(ASTNode node) {
//		if (!isMatched) {
//			int start = node.getStartPosition();
//			int end = start + node.getLength();
//			if (start == startPos && end == endPos) {// exact match
//				isMatched = true;
//				coveredNode = node;			
//			} else if (start >= startPos && end <= endPos) {//multiple statements on the same line
//				if (isSimpleStatement(node)) {
//					isMatched = true;
//					coveredNode = node;
//				}
//			} else if (start == startPos && end > endPos) {//only part of the statement (expression) is on the line
//				coveredNode = getEnclosingStatement(node);
//				isMatched = true;
//			}			
//		}
//	}
//	
//	private boolean isSimpleStatement(ASTNode node) {
//		int nodeType = node.getNodeType();
//		switch(nodeType) {
//		case ASTNode.ASSERT_STATEMENT:
//		case ASTNode.BREAK_STATEMENT:
//		case ASTNode.CONSTRUCTOR_INVOCATION:
//		case ASTNode.CONTINUE_STATEMENT:
//		case ASTNode.EMPTY_STATEMENT:
//		case ASTNode.EXPRESSION_STATEMENT:
//		case ASTNode.LABELED_STATEMENT:
//		case ASTNode.RETURN_STATEMENT:
//		case ASTNode.SUPER_CONSTRUCTOR_INVOCATION:
//		case ASTNode.SWITCH_CASE:
//		case ASTNode.THROW_STATEMENT:
//		case ASTNode.VARIABLE_DECLARATION_STATEMENT:
//			return true;
//		}
//		return false;
//	}
}
