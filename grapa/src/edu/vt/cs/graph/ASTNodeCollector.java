package edu.vt.cs.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.SourceRange;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.SynchronizedStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.WhileStatement;

public class ASTNodeCollector extends ASTVisitor{

	private Map<Integer, List<ASTNode>> lineToAsts = null;
	private Map<MethodDeclaration, SourceRange> methodToRange = null;
	private Set<String> types = null;
	private CompilationUnit cu = null;
	
	public ASTNodeCollector(CompilationUnit cu) {
		this.cu = cu;
		lineToAsts = new HashMap<Integer, List<ASTNode>>();
		methodToRange = new HashMap<MethodDeclaration, SourceRange>();
		types = new HashSet<String>();
		cu.accept(this);
	}
	
	public Map<Integer, List<ASTNode>> getLineToAsts() {
		return lineToAsts;
	}
	
	public Map<MethodDeclaration, SourceRange> getMethodToRange() {
		return methodToRange;
	}
	
	public Set<String> getTypes() {
		return types;
	}
	
	@Override
	public void preVisit(ASTNode node) {
		if (isSimpleStatement(node)) {
			addToList(node);			
		} 
	}
	
	@Override
	public boolean visit(DoStatement node) {
		addToList(node, node.getExpression());
		return true;
	}
	
	@Override
	public boolean visit(EnhancedForStatement node) { 
		addToList(node, node.getParameter(), node.getExpression());
		return true;
	}
	
	@Override
	public boolean visit(FieldDeclaration node) {
		addToList(node);
		return false;
	}
	
	@Override
	public boolean visit(ForStatement node) {
		List<ASTNode> inits = node.initializers();
		ASTNode expr = node.getExpression();
		List<ASTNode> updates = node.updaters();
		ASTNode[] nodes = new ASTNode[inits.size() + 1 + updates.size()];
		int counter = 0;
		for (; counter < inits.size(); counter++) {
			nodes[counter] = inits.get(counter);
		}
		nodes[counter++] = expr;
		for (int i = 0; i < updates.size(); i++) {
			nodes[counter + i] = updates.get(i);
		}
		addToList(node, nodes);
		return true;
	}
	
	@Override
	public boolean visit(IfStatement node) {
		addToList(node, node.getExpression());		
		return true;
	}
	
	@Override
	public boolean visit(MethodDeclaration node) { //to map all instructions which cannot be matched to any defined statements
		// such as implicit call to object.<init>
		methodToRange.put(node, new SourceRange(cu.getLineNumber(node.getStartPosition()), 
				cu.getLineNumber(node.getStartPosition() + node.getLength() - 1)));
		return true;
	}
	
	@Override
	public boolean visit(SynchronizedStatement node) {
		addToList(node, node.getExpression());
		return true;
	}
	
	@Override
	public boolean visit(SwitchStatement node) {
		addToList(node, node.getExpression());
		return true;
	}
	
	@Override
	public boolean visit(TryStatement node) {	
		addControlNode(node);
		List<CatchClause> catchClauses = node.catchClauses();
		for (CatchClause cc : catchClauses) {
			addToList(cc, cc.getException());
		}
		return true;
	}
	
	@Override
	public boolean visit(TypeDeclaration node) {
		String qName = node.resolveBinding().getQualifiedName();
		String bName = TypeNameConverter.qualifiedToBinary(qName);
		types.add(bName); //e.g., La/b/C
		return true;
	}
	
	@Override
	public boolean visit(WhileStatement node) {
		addToList(node, node.getExpression());
		return true;
	}
	
	private void addControlNode(ASTNode node) {
		int line = cu.getLineNumber(node.getStartPosition());
		if (lineToAsts.containsKey(line)) {
			lineToAsts.get(line).add(node);
		} else {
			List<ASTNode> astList = new ArrayList<ASTNode>();
			astList.add(node);
			lineToAsts.put(line, astList);
		}
	}
	
	private void addToList(ASTNode node) {
		int startPos = node.getStartPosition();
		int endPos = startPos + node.getLength() - 1;
		int line = cu.getLineNumber(startPos);
		int line2 = cu.getLineNumber(endPos);
		for (int i = line; i <= line2; i++) { //if a statement node go across multiple lines, we can still handle that
			if (lineToAsts.containsKey(i)) {
				lineToAsts.get(i).add(node);
			} else {
				List<ASTNode> astList = new ArrayList<ASTNode>();
				astList.add(node);
				lineToAsts.put(i, astList);
			}
		}		
	}	
	
	private void addToList(ASTNode nodeHolder, ASTNode...astNodes) {
		ASTNode aNode = null;
		for (int i = 0; i < astNodes.length; i++) {
			aNode = astNodes[i];
			int startPos = aNode.getStartPosition();
			int endPos = startPos + aNode.getLength() - 1;
			int line = cu.getLineNumber(startPos);
			int line2 = cu.getLineNumber(endPos);
			for (int j = line; j <= line2; j++) { //if a statement node go across multiple lines, we can still handle that
				if (lineToAsts.containsKey(j)) {
					List<ASTNode> nodes = lineToAsts.get(j);
					if (!nodes.contains(nodeHolder)) {
						nodes.add(nodeHolder);
					}					
				} else {
					List<ASTNode> astList = new ArrayList<ASTNode>();
					astList.add(nodeHolder);
					lineToAsts.put(j, astList);
				}
			}				
		}		
	}
	
	private boolean isSimpleStatement(ASTNode node) {
		int nodeType = node.getNodeType();
		switch(nodeType) {
		case ASTNode.ASSERT_STATEMENT:
		case ASTNode.BREAK_STATEMENT:
		case ASTNode.CONSTRUCTOR_INVOCATION:
		case ASTNode.CONTINUE_STATEMENT:
		case ASTNode.EMPTY_STATEMENT:
		case ASTNode.EXPRESSION_STATEMENT:
		case ASTNode.LABELED_STATEMENT:
		case ASTNode.RETURN_STATEMENT:
		case ASTNode.SUPER_CONSTRUCTOR_INVOCATION:
		case ASTNode.SWITCH_CASE:
		case ASTNode.THROW_STATEMENT:
		case ASTNode.VARIABLE_DECLARATION_STATEMENT:
			return true;
		}
		return false;
	}
}
