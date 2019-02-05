package edu.vt.cs.diffparser.tree;

import java.util.List;

import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Statement;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaMethodDeclarationNode extends JavaDeclarationNode{

	private static final long serialVersionUID = 1L;
	
	private int contentHashcode = 0;
	
	private final static int PRIME = 31;

	public JavaMethodDeclarationNode(int astNodeType, String defaultValue,
			MethodDeclaration node,
			SourceCodeRange range) {
		super(astNodeType, defaultValue, range);
		List<Statement> statements = node.getBody().statements();
		for (Statement s : statements) {
			contentHashcode = contentHashcode * PRIME + s.toString().hashCode();
		}
	}
	
	public int getContentHashcode() {
		return contentHashcode;
	}
}
