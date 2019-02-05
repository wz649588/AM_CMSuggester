package edu.vt.cs.prediction.neo;

import java.util.Enumeration;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.EmptyStatement;

import ch.uzh.ifi.seal.changedistiller.treedifferencing.Node;
import edu.vt.cs.append.JavaExpressionConverter;

public class ASTNodeToString {

	public static String convert(ASTNode node) {
		if (node instanceof EmptyStatement)
			return ";";
		JavaExpressionConverter converter = new JavaExpressionConverter();
		node.accept(converter);
		Node root = converter.getRoot();
		if (root == null)
			System.out.print("");
		Enumeration<Node> traversal = root.preorderEnumeration();
		StringBuilder builder = new StringBuilder();
		while (traversal.hasMoreElements()) {
			Node n = traversal.nextElement();
			if (n.isLeaf()) {
				builder.append(n.getValue());
			}
		}
		return builder.toString();
	}
}
