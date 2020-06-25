package edu.vt.cs.graph;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.PackageDeclaration;

public class PackageDetector extends ASTVisitor{

	public String packageName = null;
	public PackageDetector(ASTNode cu) {
		cu.accept(this);
	}
	
	@Override
	public boolean visit(PackageDeclaration node) {
		packageName = node.getName().getFullyQualifiedName();
		return false;
	}
}
