package org.eclipse.jdt.core.dom;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.TypeDeclaration;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

public class MethodInvocationUtil {
	public static SimpleName getName(ASTNode node) {
		SimpleName sName = null;
		if (node instanceof MethodInvocation) {
			sName = ((MethodInvocation)node).getName();
		} else if (node instanceof SuperMethodInvocation) {
			sName = ((SuperMethodInvocation)node).getName();
		}
		return sName;
	}
	
	public static IMethodBinding getMethodBinding(ASTNode node) {
		IMethodBinding methodBinding = null;
		if (node instanceof MethodInvocation) {
			methodBinding = ((MethodInvocation)node).resolveMethodBinding();
		} else if (node instanceof SuperMethodInvocation) {
			methodBinding = ((SuperMethodInvocation)node).resolveMethodBinding();
		}
		return methodBinding;
	}
	
	@SuppressWarnings("unchecked")
	public static List getArguments(ASTNode node) {
		List arguments = null;
		if (node instanceof MethodInvocation) {
			arguments = ((MethodInvocation)node).arguments();
		} else if (node instanceof SuperMethodInvocation) {
			arguments = ((SuperMethodInvocation)node).arguments();
		}
		return arguments;
	}
	
	public static ASTNode getContainer(ASTNode node) {
		ASTNode container = null;
		if (node instanceof MethodInvocation) {
			container = PPAASTUtil.getContainer((MethodInvocation)node);
		} else if (node instanceof SuperMethodInvocation) {
			container = PPAASTUtil.getSpecificParentType(node, ASTNode.TYPE_DECLARATION);
			if (container != null) {
				TypeDeclaration td = (TypeDeclaration) container;
				container = td.getSuperclassType();
			}
		}
		return container;
	}
}
