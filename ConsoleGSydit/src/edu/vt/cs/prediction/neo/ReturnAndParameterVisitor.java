
package edu.vt.cs.prediction.neo;


import java.util.List;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.VariableDeclaration;



public class ReturnAndParameterVisitor extends ASTVisitor{
	
	private MethodDeclaration methodDeclaration;
	
	private Set<String> parameterSet = new HashSet<>();
	
	private String returnType;
	
	
	
	public ReturnAndParameterVisitor (ASTNode methodBody) {
		this.methodDeclaration = (MethodDeclaration)methodBody;
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {
		Type typeOfAm = node.getReturnType2();
		if(typeOfAm != null){
			ITypeBinding iBinding = typeOfAm.resolveBinding();
			returnType = iBinding.getQualifiedName();
		}
		List<?> parameters = node.parameters();
		for(int i = 0; i < parameters.size(); i++){
			VariableDeclaration var = (VariableDeclaration) parameters.get(i);
			parameterSet.add(dealWithType(var.resolveBinding().getType().getQualifiedName()));
		}
		return false;
	}
//	
	
	String dealWithType(String type){
//		if (type.contains("<")){
//			return type.substring(0, type.indexOf('<'));
//		}
		if(!parameterSet.contains(type)) return type;
		int i = 1;
		for(i = 1; i < 100; i++){
			if(!parameterSet.contains(type + i)) break;
		}
		return type + i;
	}
//	
	public void execute() {
		methodDeclaration.accept(this);
	}
	
	public String getReturnType() {
		return returnType;
	}
	
	public Set<String> getParameters() {
		return parameterSet;
	}
}
