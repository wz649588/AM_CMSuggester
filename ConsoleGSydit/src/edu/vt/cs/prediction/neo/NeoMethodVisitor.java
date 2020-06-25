package edu.vt.cs.prediction.neo;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
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



public class NeoMethodVisitor extends ASTVisitor{
	
	private ASTNode methodDeclaration;
	
	private Set<String> methodSet = new HashSet<String>();
	
//	Map<String, Set<String>> classToMethodsMap = new HashMap<>();
	
	
	
	public NeoMethodVisitor(ASTNode methodBody) {
		this.methodDeclaration = methodBody;
		
	}
	
	@Override
	public boolean visit(MethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
		
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null) {
				String methodName = node.getName().toString();
				String className = tBinding.getQualifiedName();
//				if (!classToMethodsMap.containsKey(className)) classToMethodsMap.put(className, new HashSet<String>());
//				classToMethodsMap.get(className).add(className + methodName);
				methodSet.add(className + methodName);
			}
		}
		return false;
	}
	
	
	@Override
	public boolean visit(SuperMethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){ //&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null) {
				String methodName = node.getName().toString();
				String className = tBinding.getQualifiedName();
//				if (!classToMethodsMap.containsKey(className)) classToMethodsMap.put(className, new HashSet<String>());
//				classToMethodsMap.get(className).add(className + methodName);
				methodSet.add(className + methodName);
			}
		}
		return false;
	}

	
//	@Override
//	public boolean visit(QualifiedName node){
//		IBinding binding = node.resolveBinding();
//		if (binding != null && binding instanceof IMethodBinding){
//			IMethodBinding vBinding = (IMethodBinding) binding;
////			if (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod()) {
//			ITypeBinding tBinding = vBinding.getDeclaringClass();
//			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
//				String methodName = node.getName().toString();
//				methodSet.add(methodName);
//			}
////			}
//		}
//		return false;
//	}
//	
//	
//	@Override
//	public boolean visit(MethodReference node){
//		IBinding binding = node.resolveBinding();
//		if (binding != null && binding instanceof IMethodBinding){
//			IMethodBinding vBinding = (IMethodBinding) binding;
////			if (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod()) {
//			ITypeBinding tBinding = vBinding.getDeclaringClass();
//			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
//				String methodName = node.getName().getIdentifier();
//				methodSet.add(methodName);
//			}
////			}
//		}
//		return false;
//	}
	
	
	public void execute() {
		if (methodDeclaration instanceof MethodDeclaration) {
			ASTNode body = ((MethodDeclaration) methodDeclaration).getBody();
			if (body != null)
				body.accept(this);
		} else {
			methodDeclaration.accept(this);
		}
	}
	
	public Set<String> getMethods() {
		
////		int maxNumMethods = -1;
//		for (String className : classToMethodsMap.keySet()){
//			if(classToMethodsMap.get(className).size() > maxNumMethods) maxNumMethods = classToMethodsMap.get(className).size();
//		}
//		if(maxNumMethods >= 2){
//			for(String className : classToMethodsMap.keySet()) {
//				if (classToMethodsMap.get(className).size() == maxNumMethods) {
//					methodSet.addAll(classToMethodsMap.get(className));
//				}
//			}
//		}
		return methodSet;
	}
}