package edu.vt.cs.prediction.neo;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperFieldAccess;

/**
 * Check if the statement contains AF
 * @author Ye Wang
 * @since 07/09/2017
 *
 */
public class AFStatementChecker extends ASTVisitor {
	
	private boolean statementContainsAF = false;
	
	private ASTNode statement;
	
	private String afName;
	
	private String classSig;

	public AFStatementChecker(ASTNode statement, String afName, String classSig) {
		this.statement = statement;
		this.afName = afName;
		this.classSig = classSig;
	}
	
	@Override
	public boolean visit(FieldAccess node) {
		IVariableBinding vBinding = node.resolveFieldBinding();
		if (vBinding != null && vBinding.isField()) {
			ITypeBinding tBinding = vBinding.getDeclaringClass();
			if (tBinding != null && tBinding.getQualifiedName().equals(classSig)) {
				String fieldName = node.getName().toString();
				if (fieldName.equals(afName))
					statementContainsAF = true;
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
				if (fieldName.equals(afName))
					statementContainsAF = true;
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
					if (fieldName.equals(afName))
						statementContainsAF = true;
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
					if (fieldName.equals(afName))
						statementContainsAF = true;
				}
			}
		}
		return false;
	}
	
	public boolean containsAF() {
		statement.accept(this);
		
		return statementContainsAF;
	}
}
