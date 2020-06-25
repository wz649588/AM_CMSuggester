package edu.vt.cs.prediction.neo;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
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



public class MethodNameVisitor extends ASTVisitor{
	
	private ASTNode methodDeclaration;
	
	private String classSig;
	
	private Set<String> methodSet = new HashSet<String>();
	
	
	
	public MethodNameVisitor(ASTNode methodBody, String classSig) {
		this.methodDeclaration = methodBody;
		this.classSig = classSig;
	}
	
	@Override
	public boolean visit(MethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
		
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
//			if (tBinding != null) {
				String methodName = node.getName().toString();
				methodSet.add(classSig + methodName);
			}
		}
		return false;
	}
	
	
	@Override
	public boolean visit(SuperMethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){ //&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
//			if (tBinding != null) {
				String methodName = node.getName().toString();
				methodSet.add(classSig + methodName);
			}
		}
		return false;
	}
	
/*
 * Added on Mar.4 constructor invocation
 */
//	@Override
//	public boolean visit(ConstructorInvocation node){
//		IMethodBinding vBinding = node.resolveConstructorBinding();
//		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
//		
//			ITypeBinding tBinding = vBinding.getDeclaringClass();
//			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
////			if (tBinding != null) {
//				String methodName = vBinding.getName().toString();
////				try{
////					System.out.println(methodName + " This is a constructor invocation name, Let us try if it works");
////				    Thread thread = Thread.currentThread();
////				    thread.sleep(10000);//暂停1.5秒后程序继续执行
////				}catch (InterruptedException e) {
////				    // TODO Auto-generated catch block
////				    e.printStackTrace();
////				}
//				methodSet.add(classSig + methodName);
//			}
//		}
//		return false;
//	}

	
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
		return methodSet;
	}
}
