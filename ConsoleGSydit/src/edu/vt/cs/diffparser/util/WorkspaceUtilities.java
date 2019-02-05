package edu.vt.cs.diffparser.util;

import java.util.List;

import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;

public class WorkspaceUtilities {

	public static final String SEPARATOR_BETWEEN_PARAMETERS = ", ";
	
	/**
	 * The method name is the unique ID for the method
	 * 
	 * @param node
	 * @return
	 */
	public static String getMethodSignatureFromASTNode(MethodDeclaration node) {
		StringBuffer name = new StringBuffer(node.getName().getIdentifier());
		name.append("(");
		List<SingleVariableDeclaration> parameters = node.parameters();
		int numOfComma = node.parameters().size() - 1;
		int counter = 0;
		for (SingleVariableDeclaration parameter : parameters) {
			String typeName = parameter.getType().toString();
			name.append(typeName);
			if (counter++ < numOfComma) {
				name.append(SEPARATOR_BETWEEN_PARAMETERS);
			}
		}
		name.append(")");
		return name.toString();
	}
}
