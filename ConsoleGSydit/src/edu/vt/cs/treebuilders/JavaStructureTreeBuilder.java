package edu.vt.cs.treebuilders;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AnnotationTypeDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import edu.vt.cs.diffparser.tree.JavaCUNode;
import edu.vt.cs.diffparser.tree.JavaDeclarationNode;
import edu.vt.cs.diffparser.tree.JavaFieldDeclarationNode;
import edu.vt.cs.diffparser.tree.JavaMethodDeclarationNode;
import edu.vt.cs.diffparser.tree.JavaStructureNode;
import edu.vt.cs.diffparser.tree.JavaTypeDeclarationNode;
import edu.vt.cs.diffparser.util.Pair;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import edu.vt.cs.diffparser.util.WorkspaceUtilities;

public class JavaStructureTreeBuilder extends AbstractTreeBuilder<JavaStructureNode>{	
	
	private String fileName;
	
	private String packageName = null;
	
	CompilationUnit cu = null;
	
	public void init(String fileName) {
		this.fileName = fileName;
	}
	
	@Override
	public boolean visit(CompilationUnit node) {
		fNodeStack = new Stack<JavaStructureNode>();
		root = new JavaCUNode(node.getNodeType(), fileName, null, node);
		cur = root;
		fNodeStack.push(cur);
		return true;
	}
	
	@Override
	public void endVisit(CompilationUnit node) {
		fNodeStack.pop();
		cur = null;
	}
	
	@Override
	public boolean visit(FieldDeclaration node) {
		Type t = node.getType();
		String typeName = null;
		try {
			typeName = t.resolveBinding().getQualifiedName();
		} catch (Exception e) {// the type cannot be resolved
			typeName = t.toString();
		}		
		List<VariableDeclarationFragment> frags = node.fragments();
		for (VariableDeclarationFragment frag : frags) {
			JavaFieldDeclarationNode n = new JavaFieldDeclarationNode(
					node.getNodeType(),
					typeName, frag.getName().getIdentifier(),
					new SourceCodeRange(node.getStartPosition(), node.getLength()));
			((JavaTypeDeclarationNode)cur).addField(n);
		}
		return false;
	}
	
	@Override
	public boolean visit(ImportDeclaration node) {
		((JavaCUNode)root).addImport(node.getName().getFullyQualifiedName());
		return false;
	}
	
	
	@Override
	public boolean visit(MethodDeclaration node) {
		JavaMethodDeclarationNode n = new JavaMethodDeclarationNode(node.getNodeType(), 
				WorkspaceUtilities.getMethodSignatureFromASTNode(node), node,
				new SourceCodeRange(node.getStartPosition(), node.getLength()));
		((JavaTypeDeclarationNode)cur).addMethod(n);
		return false;
	}
	
	//To be extended later
	@Override
	public boolean visit(EnumDeclaration node) {
		return false;
	}
	
	//To be extended later
	@Override
	public boolean visit(AnnotationTypeDeclaration node) {
		return false;
	}
	
	@Override
	public boolean visit(PackageDeclaration node) {	
		packageName = node.getName().getFullyQualifiedName();
		((JavaCUNode)root).setPackageName(packageName);
		return false;
	}
	
	@Override
	public boolean visit(TypeDeclaration node) {
		String className = null;
		try {
			className = node.resolveBinding().getQualifiedName();
		} catch (Exception e) {// the type cannot be resolved
			className = node.getName().getIdentifier();
		}
		String qualifiedName = null;
		if (packageName.isEmpty() || className.startsWith(packageName)) {
			qualifiedName = className;
		} else {			
			if (cur instanceof JavaTypeDeclarationNode) {
				qualifiedName = cur.getStrValue() + "." + className;
			} else {
				qualifiedName = packageName + "." + className;
			}
		}
		
		JavaTypeDeclarationNode n = new JavaTypeDeclarationNode(node.getNodeType(), qualifiedName,
				new SourceCodeRange(node.getStartPosition(), node.getLength()));
		n.isInterface = node.isInterface();
		if (node.getSuperclassType() != null) {
			if (node.getSuperclassType().resolveBinding() == null) {
				n.superName = node.getSuperclassType().toString();
			} else {
				n.superName = node.getSuperclassType().resolveBinding().getQualifiedName();
			}
		}		
		if (node.superInterfaceTypes() != null) {
			if (n.interfaces.isEmpty()) {
				n.interfaces = new ArrayList<String>();
			}
			for (Type type : (List<Type>) node.superInterfaceTypes()) {
				try {
					n.interfaces.add(type.resolveBinding().getQualifiedName());
				} catch (Exception e) {
					n.interfaces.add(type.toString());
				}
			}
		}		
		cur.add(n);
		fNodeStack.push(n);
		cur = n;
		return true;
	}

	@Override
	public void endVisit(TypeDeclaration node) {
		fNodeStack.pop();
		cur = fNodeStack.peek();
	}
}
