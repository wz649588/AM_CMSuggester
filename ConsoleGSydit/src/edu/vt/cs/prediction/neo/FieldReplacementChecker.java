package edu.vt.cs.prediction.neo;

import java.util.HashSet;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;

import ch.uzh.ifi.seal.changedistiller.model.classifiers.java.JavaEntityType;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.Node;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;
import edu.vt.cs.append.JavaExpressionConverter;
import edu.vt.cs.append.NodeUtility;
import edu.vt.cs.append.TopDownTreeMatcher;
import edu.vt.cs.diffparser.util.SourceCodeRange;

/**
 * 
 * @author Ye Wang
 * @since 06/08/2017
 */
public class FieldReplacementChecker {
	
	private FieldReplacementDatabaseInserter dbInserter;
	
	private TopDownTreeMatcher matcher;

	private HashSet<NodePair> matches;
	
	private ASTNode leftMethodBody;
	
	private ASTNode rightMethodBody;
	
	private HashSet<NodePair> processedMatches;
	
	public FieldReplacementChecker(FieldReplacementDatabaseInserter dbInserter,
			TopDownTreeMatcher matcher,
			HashSet<NodePair> matches, ASTNode leftMethodBody, ASTNode rightMethodBody) {
		this.dbInserter = dbInserter;
		this.matcher = matcher;
		this.leftMethodBody = leftMethodBody;
		this.rightMethodBody = rightMethodBody;
		this.matches = matches;
		// Removes node pairs whose two nodes are same.
		processedMatches = new HashSet<NodePair>();
		for (NodePair pair: matches) {
			Node left = pair.getLeft();
			Node right = pair.getRight();
			if (!left.toString().equals(right.toString())) {
				processedMatches.add(pair);
			}
		}
	}
	
	/**
	 * Check field replacement
	 * Add data into database
	 * @return
	 */
	public boolean execute() {
//		StatementVisitor stmtVisitor = new StatementVisitor();
		AstNodeVisitor nodeVisitor = new AstNodeVisitor();
		for (NodePair pair: processedMatches) {
			Node left = pair.getLeft();
			Node right = pair.getRight();
			
//			ASTNode leftAst = ASTNodeBuilder.convert(left);
//			ASTNode rightAst = ASTNodeBuilder.convert(right);
			
//			SourceCodeRange.convert(left.getEntity());
			
			SourceCodeRange leftCodeRange = SourceCodeRange.convert(left.getEntity());
			SourceCodeRange rightCodeRange = SourceCodeRange.convert(right.getEntity());
			
//			ASTNode leftAst1 = stmtVisitor.lookForNode(leftMethodBody, leftCodeRange);
//			ASTNode rightAst1 = stmtVisitor.lookForNode(rightMethodBody, rightCodeRange);
			
			ASTNode leftAst = nodeVisitor.lookForNode(leftMethodBody, leftCodeRange);
			ASTNode rightAst = nodeVisitor.lookForNode(rightMethodBody, rightCodeRange);
			
			if (leftAst == null || rightAst == null)
				continue;
			
			JavaExpressionConverter leftConverter = new JavaExpressionConverter();
			leftAst.accept(leftConverter);
			Node leftRoot = leftConverter.getRoot();
			JavaExpressionConverter.markSubStmts(leftRoot, leftAst);
			JavaExpressionConverter rightConverter = new JavaExpressionConverter();
			rightAst.accept(rightConverter);
			Node rightRoot = rightConverter.getRoot();
			JavaExpressionConverter.markSubStmts(rightRoot, rightAst);
			
			
//			TopDownTreeMatcher matcher = new TopDownTreeMatcher();
			matcher.match2(leftRoot, rightRoot);
//			Map<Node, Node> unmatchedLeftToRight = matcher.getUnmatchedLeftToRight();
//			for (Map.Entry<Node, Node> entry: unmatchedLeftToRight.entrySet()) {
//				Node lNode = entry.getKey();
//				Node rNode = entry.getValue();
//				System.out.println("unmatchedLeftToRight");
//				System.out.println(lNode);
//				System.out.println(rNode);
//			}
			
//			for (Map.Entry<Node, Node> entry: matcher.leftToRightOtherClassField.entrySet()) {
//				Node lNode = entry.getKey();
////				Node 
//			}
			
			insertIntoDatabase("other_class_field", matcher.leftToRightOtherClassField);
			insertIntoDatabase("same_class_field", matcher.leftToRightSameClassField);
			insertIntoDatabase("string_literal", matcher.leftToRightStringLiteral);
			insertIntoDatabase("number_literal", matcher.leftToRightNumberLiteral);
			insertIntoDatabase("boolean_literal", matcher.leftToRightBooleanLiteral);
			insertIntoDatabase("null_literal", matcher.leftToRightNullLiteral);
			insertIntoDatabase("character_literal", matcher.leftToRightCharacterLiteral);
			
		}
		
		return false;
	}
	
	private void insertIntoDatabase(String rpType, Map<Node, Node> leftToRight) {
		for (Map.Entry<Node, Node> entry: leftToRight.entrySet()) {
			Node lNode = entry.getKey();
			Node rNode = entry.getValue();
			String oldEntityName = null;
			String newEntityName = null;
			if (lNode.getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
				Node lFirst = (Node) lNode.getChildAt(0);
				Node lSecond = (Node) lNode.getChildAt(1);
				Node lThird = (Node) lNode.getChildAt(2);
				oldEntityName = lFirst.getValue() + lSecond.getValue() + lThird.getValue();
			} else {
				oldEntityName = lNode.getValue();
			}
			if (rNode.getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
				Node rFirst = (Node) rNode.getChildAt(0);
				Node rSecond = (Node) rNode.getChildAt(1);
				Node rThird = (Node) rNode.getChildAt(2);
				newEntityName = rFirst.getValue() + rSecond.getValue() + rThird.getValue();
			} else {
				newEntityName = rNode.getValue();
			}
			dbInserter.execute(rpType, oldEntityName, newEntityName);
		}
	}
	
}
