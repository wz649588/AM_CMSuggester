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
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperFieldAccess;

/**
 * Get used field names from a method
 * @author Ye Wang
 * @since 06/28/2017
 *
 */
public class FieldNameVisitor extends ASTVisitor {

	private ASTNode methodDeclaration;
	
	private String classSig;
	
	private Set<String> readFieldSet = new HashSet<String>();
	
	private Set<String> writtenFieldSet = new HashSet<String>();
	
	private Set<String> fieldSet = new HashSet<String>();
	
	public FieldNameVisitor(ASTNode methodBody, String classSig) {
		this.methodDeclaration = methodBody;
		this.classSig = classSig;
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
		if (vBinding != null && vBinding.isField()) {
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
				String fieldName = node.getName().toString();
				if (isLeftSide(node)) {
					writtenFieldSet.add(fieldName);
				} else {
					readFieldSet.add(fieldName);
				}
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(SuperFieldAccess node) {
		IVariableBinding vBinding = node.resolveFieldBinding();
		if (vBinding != null && vBinding.isField()) {
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
				String fieldName = node.getName().toString();
				if (isLeftSide(node)) {
					writtenFieldSet.add(fieldName);
				} else {
					readFieldSet.add(fieldName);
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
			if (vBinding.isField()) {
				ITypeBinding tBinding = vBinding.getDeclaringClass();
				if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
					String fieldName = node.getName().toString();
					if (isLeftSide(node)) {
						writtenFieldSet.add(fieldName);
					} else {
						readFieldSet.add(fieldName);
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
			if (vBinding.isField()) {
				ITypeBinding tBinding = vBinding.getDeclaringClass();
				if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
					String fieldName = node.getIdentifier();
					if (isLeftSide(node)) {
						writtenFieldSet.add(fieldName);
					} else {
						readFieldSet.add(fieldName);
					}
				}
			}
		}
		return false;
	}
	
	public void execute() {
		if (methodDeclaration instanceof MethodDeclaration) {
			ASTNode body = ((MethodDeclaration) methodDeclaration).getBody();
			if (body != null)
				body.accept(this);
		} else {
			methodDeclaration.accept(this);
		}
		
		fieldSet.addAll(readFieldSet);
		fieldSet.addAll(writtenFieldSet);
	}
	
	public Set<String> getReadFields() {
		return readFieldSet;
	}
	
	public Set<String> getWrittenFields() {
		return writtenFieldSet;
	}
	
	public Set<String> getFields() {
		return fieldSet;
	}
	
	
}
