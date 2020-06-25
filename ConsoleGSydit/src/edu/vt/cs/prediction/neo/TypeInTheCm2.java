/*
 * get all the types including the return type of the invoked methods and the types of 
 * all the leftside variables. If they include the return type of the AM and the arguments type 
 * include all of them , THEN they are 
 * more likely to invoke the am.
 */

package edu.vt.cs.prediction.neo;


import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.MethodRef;
import org.eclipse.jdt.core.dom.MethodReference;
import org.eclipse.jdt.core.dom.ThrowStatement;



public class TypeInTheCm2 extends ASTVisitor{
	
	private ASTNode methodDeclaration;
	
	private Set<String> typeSet = new HashSet<String>();
	
	private Set<String> typeSetAll = new HashSet<String>();
	
	
	
	public TypeInTheCm2(ASTNode methodBody) {
		this.methodDeclaration = methodBody;
	}
	
	@Override
	public boolean visit(MethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			
			ITypeBinding tBinding = vBinding.getReturnType();
			if (tBinding != null) {
				typeSet.add(dealWithType(tBinding.getQualifiedName()));
				typeSetAll.add(dealWithType(tBinding.getQualifiedName()));
			}
		}
		return false;
	}
	
	
	@Override
	public boolean visit(SuperMethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){ //&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			
			ITypeBinding tBinding = vBinding.getReturnType();
			if (tBinding != null) {
				typeSet.add(dealWithType(tBinding.getQualifiedName()));
				typeSetAll.add(dealWithType(tBinding.getQualifiedName()));
			}
		}
		return false;
	}
	
	/**
	 * Check if the node is the left side of an assignment
	 * @param node
	 * @return
	 */
	private static boolean isLeftSide(ASTNode node) {
		ASTNode parent = node.getParent();
		if (parent instanceof Assignment) {
			Assignment assignment = (Assignment) parent;
			if (assignment.getLeftHandSide().equals(node))
				return true;
		}
		return false;
	}
	
	@Override
	public boolean visit(FieldAccess node) {
		IVariableBinding vBinding = node.resolveFieldBinding();
		if (vBinding != null) {
			ITypeBinding tBinding = vBinding.getType();
			if (tBinding != null) {
				String typeName = dealWithType(tBinding.getQualifiedName());
				typeSetAll.add(typeName);
				if (isLeftSide(node)) {
					typeSet.add(typeName);
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(SuperFieldAccess node) {
		IVariableBinding vBinding = node.resolveFieldBinding();
		if (vBinding != null) {
			ITypeBinding tBinding = vBinding.getType();
			if (tBinding != null) {
				String typeName = dealWithType(tBinding.getQualifiedName());
				typeSetAll.add(typeName);
				if (isLeftSide(node)) {
					typeSet.add(typeName);
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(QualifiedName node) {
		IBinding binding = node.resolveBinding();
		if (binding != null && binding instanceof IVariableBinding) {
			IVariableBinding vBinding = (IVariableBinding) binding;
			if (vBinding != null) {
				ITypeBinding tBinding = vBinding.getType();
				if (tBinding != null) {
					String typeName = dealWithType(tBinding.getQualifiedName());
					typeSetAll.add(typeName);
					if (isLeftSide(node)) {
						typeSet.add(typeName);
					}
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(SimpleName node) {
		IBinding binding = node.resolveBinding();
		if (binding != null && binding instanceof IVariableBinding) {
			IVariableBinding vBinding = (IVariableBinding) binding;
			if (vBinding != null) {
				ITypeBinding tBinding = vBinding.getType();
				if (tBinding != null) {
					String typeName = dealWithType(tBinding.getQualifiedName());
					typeSetAll.add(typeName);
					if (isLeftSide(node)) {
						typeSet.add(typeName);
					}
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(ThrowStatement node) {
		ITypeBinding binding = node.getExpression().resolveTypeBinding();
		if (binding != null) {
			String typeName = dealWithType(binding.getQualifiedName());
			typeSetAll.add(typeName);
		}
		return false;
	}
	
	String dealWithType(String type){
		if (type.contains("<")){
			return type.substring(0, type.indexOf('<'));
		}
		return type;
	}
	
	
	public void execute() {
		if (methodDeclaration instanceof MethodDeclaration) {
			ASTNode body = ((MethodDeclaration) methodDeclaration).getBody();
			if (body != null)
				body.accept(this);
		} else {
			methodDeclaration.accept(this);
		}
	}
	
	public Set<String> getTypes() {
		return typeSet;
	}
	
	public Set<String> getTypesAll() {
		return typeSetAll;
	}
}


