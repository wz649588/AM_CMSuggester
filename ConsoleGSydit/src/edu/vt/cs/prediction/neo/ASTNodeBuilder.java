package edu.vt.cs.prediction.neo;

import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;

import ch.uzh.ifi.seal.changedistiller.treedifferencing.Node;

public class ASTNodeBuilder {

	public static ASTNode convert(Node n) {
		String value = n.getValue();
		return convert(value);
	}
	
	private static ASTNode convert(String value) {
		ASTParser parser = ASTParser.newParser(AST.JLS8);
		parser.setSource(value.toCharArray());
		parser.setKind(ASTParser.K_STATEMENTS);
		return parser.createAST(null);
	}
	
}
