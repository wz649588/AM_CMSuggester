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



public class AmCmMethodNameVisitor extends ASTVisitor{
	
	private ASTNode methodDeclaration;
	
	private String classSig;
	
	private String cmClassSig;
	
	private Set<String> methodSet = new HashSet<String>();
	
	public AmCmMethodNameVisitor(ASTNode methodBody, String classSig, String cmClassSig) {
		this.methodDeclaration = methodBody;
		this.classSig = classSig;
		this.cmClassSig = cmClassSig;
	}
	
	@Override
	public boolean visit(MethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){//&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			System.out.println("Can it go through here??????");
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && (tBinding.getQualifiedName().equals(classSig) || tBinding.getQualifiedName().equals(cmClassSig))) {
//			if (tBinding != null) {
				String methodName = node.getName().toString();
				methodSet.add(methodName);
			}
		}
		return false;
	}
	
	
	@Override
	public boolean visit(SuperMethodInvocation node){
		IMethodBinding vBinding = node.resolveMethodBinding();
		if (vBinding != null){ //&& (vBinding.isParameterizedMethod() || vBinding.isGenericMethod() || vBinding.isConstructor() || vBinding.isRawMethod())) {
			System.out.println("Can it go through here, too??????");
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && (tBinding.getQualifiedName().equals(classSig) || tBinding.getQualifiedName().equals(cmClassSig))) {
//			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
//			if (tBinding != null) {
				String methodName = node.getName().toString();
				methodSet.add(methodName);
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
		return methodSet;
	}
}