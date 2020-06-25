/*
 * get all the types including the return type of the invoked methods and the types of 
 * all the leftside variables. If they include the return type of the AM and the arguments type 
 * include all of them , THEN they are 
 * more likely to invoke the am.
 */

package edu.vt.cs.prediction.neo;


import java.util.HashSet;
import java.util.List;
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
import org.eclipse.jdt.core.dom.VariableDeclaration;



public class TypeInTheCm extends ASTVisitor{
	
	private ASTNode methodDeclaration;
	
	private Set<String> typeSetAll = new HashSet<String>();
	
	private Set<String> typeForPar = new HashSet<String>();
	
	
	
	public TypeInTheCm(ASTNode methodBody) {
		this.methodDeclaration = methodBody;
	}
	
	@Override
	public boolean visit(MethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			
			ITypeBinding tBinding = vBinding.getReturnType();
			if (tBinding != null) {
				typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
				typeSetAll.add(dealWithType1(tBinding.getQualifiedName()));
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
				typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
				typeSetAll.add(dealWithType1(tBinding.getQualifiedName()));
			}
		}
		return false;
	}
	
	/**
	 * Check if the node is the left side of an assignment
	 * @param node
	 * @return
	 */
//	private static boolean isLeftSide(ASTNode node) {
//		ASTNode parent = node.getParent();
//		if (parent instanceof Assignment) {
//			Assignment assignment = (Assignment) parent;
//			if (assignment.getLeftHandSide().equals(node))
//				return true;
//		}
//		return false;
//	}
	
	@Override
	public boolean visit(FieldAccess node) {
		IVariableBinding vBinding = node.resolveFieldBinding();
		if (vBinding != null) {
			ITypeBinding tBinding = vBinding.getType();
			if (tBinding != null) {
				String typeName = dealWithType1(tBinding.getQualifiedName());
				typeSetAll.add(typeName);
				typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
//				if (isLeftSide(node)) {
//					typeSet.add(typeName);
//				}
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
				String typeName = dealWithType1(tBinding.getQualifiedName());
				typeSetAll.add(typeName);
				typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
//				if (isLeftSide(node)) {
//					typeSet.add(typeName);
//				}
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
					String typeName = dealWithType1(tBinding.getQualifiedName());
					typeSetAll.add(typeName);
					typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
//					if (isLeftSide(node)) {
//						typeSet.add(typeName);
//					}
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
					String typeName = dealWithType1(tBinding.getQualifiedName());
					typeSetAll.add(typeName);
					typeForPar.add(dealWithType2(tBinding.getQualifiedName()));
//					if (isLeftSide(node)) {
//						typeSet.add(typeName);
//					}
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(ThrowStatement node) {
		ITypeBinding binding = node.getExpression().resolveTypeBinding();
		if (binding != null) {
			String typeName = dealWithType1(binding.getQualifiedName());
			typeSetAll.add(typeName);
			typeForPar.add(dealWithType2(binding.getQualifiedName()));
		}
		return false;
	}
	
	String dealWithType1(String type){
//		if (type.contains("<")){
//			return type.substring(0, type.indexOf('<'));
//		}
		if(!typeSetAll.contains(type)) return type;
		int i = 1;
		for(i = 1; i < 100; i++){
			if(!typeSetAll.contains(type + i)) break;
		}
		return type + i;
	}
	
	String dealWithType2(String type){
//		if (type.contains("<")){
//			return type.substring(0, type.indexOf('<'));
//		}
		if(!typeForPar.contains(type)) return type;
		int i = 1;
		for(i = 1; i < 100; i++){
			if(!typeForPar.contains(type + i)) break;
		}
		return type + i;
	}
	
	
	public void execute() {
		if (methodDeclaration instanceof MethodDeclaration) {
			List<?> parameters = ((MethodDeclaration)methodDeclaration).parameters();
			for(int i = 0; i < parameters.size(); i++){
				VariableDeclaration var = (VariableDeclaration) parameters.get(i);
				typeForPar.add(dealWithType2(var.resolveBinding().getType().getQualifiedName()));
			}
			ASTNode body = ((MethodDeclaration) methodDeclaration).getBody();
			if (body != null)
				body.accept(this);
		} else {
			methodDeclaration.accept(this);
		}
	}
	
	public Set<String> getTypesPar() {
		return typeForPar;
	}
	
	public Set<String> getTypesAll() {
		return typeSetAll;
	}
}


