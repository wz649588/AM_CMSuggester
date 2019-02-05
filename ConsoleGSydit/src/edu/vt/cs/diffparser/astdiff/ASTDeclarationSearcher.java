package edu.vt.cs.diffparser.astdiff;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.AnnotationTypeDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;

import edu.vt.cs.diffparser.util.Range;

public class ASTDeclarationSearcher extends ASTVisitor{

	CompilationUnit cu = null;
	List<Range> ranges = null;
	Range cur = null;
	int index = 0;
	int size = 0;
	List<List<ASTNode>> declarationsList = new ArrayList<List<ASTNode>>();
	List<ASTNode> declarations = null;
	
	public List<List<ASTNode>> findElements(CompilationUnit node, List<Range> ranges) {
		this.ranges = ranges;
		index = 0;
		size = ranges.size();
		declarations = new ArrayList<ASTNode>();
		declarationsList.add(declarations);
		cur = ranges.get(index);
		cu = node;
		cu.accept(this);
		return declarationsList;
	}
	
	private boolean update() {
		index++;
		if (index == size)
			return false;		
		cur = ranges.get(index);
		declarations = new ArrayList<ASTNode>();
		declarationsList.add(declarations);
		return true;
	}
	
	private boolean visitSimpleDeclaration(ASTNode node) {
		Range r = getAndAdjustLineRange(node);
		if (r == null) 
			return false;
		if (r.getStart() >= cur.getStart()) {
			declarations.add(node); // find a single line-involved change			
		}
		return false;
	}
	
	private boolean visitComplexDeclaration(ASTNode node) {
		Range r = getAndAdjustLineRange(node);
		if (r == null) {
			return false;
		}
		if (r.before(cur)) {
			return false;
		} 
		if (r.isIncluded(cur)) {
			declarations.add(node);
			return false;
		}
		switch(node.getNodeType()) {
		case ASTNode.ANNOTATION_TYPE_DECLARATION:
		case ASTNode.ENUM_DECLARATION:
		case ASTNode.TYPE_DECLARATION: 
			visitSimpleDeclaration(((AbstractTypeDeclaration)node).getName());
			break;
		}
		return true;
	}
	
	
	private Range getAndAdjustLineRange(ASTNode node) {
		int sPosition = node.getStartPosition();
		int s = cu.getLineNumber(sPosition) - 1;
		int e = cu.getLineNumber(sPosition + node.getLength()) - 1;
		Range r = new Range(s, e);
		boolean flag = false;
		while (r.after(cur)) {
			flag = update();
			if (flag) {
				break;
			}
			return null; // no new range available
		}// skip all textual diff which is before the current AST node
		return new Range(s, e);
	}
	
	public boolean visit(PackageDeclaration node) {		
		return visitSimpleDeclaration(node);
	} 
	
	public boolean visit(ImportDeclaration node) {
		return visitSimpleDeclaration(node);
	}
	
	public boolean visit(TypeDeclaration node) {
		return visitComplexDeclaration(node);
	}
	
	public boolean visit(EnumDeclaration node) {
		return visitComplexDeclaration(node);
	}
	
	public boolean visit(AnnotationTypeDeclaration node) {
		return visitComplexDeclaration(node);
	}
	
	public boolean visit(FieldDeclaration node) {
		return visitSimpleDeclaration(node);
	}
	
	public boolean visit(MethodDeclaration node) {
		return visitSimpleDeclaration(node);
	}
}
