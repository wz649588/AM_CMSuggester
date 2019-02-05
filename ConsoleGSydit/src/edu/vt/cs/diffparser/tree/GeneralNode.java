package edu.vt.cs.diffparser.tree;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.tree.DefaultMutableTreeNode;

import org.eclipse.jdt.core.dom.ASTNode;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class GeneralNode extends DefaultMutableTreeNode{

	private static final long serialVersionUID = 1L;

	protected int astNodeType;
	
	protected SourceCodeRange range;
	
	protected String strValue;
	
	private boolean matched;
	
	public GeneralNode(int astNodeType, String value, SourceCodeRange range) {
		this.astNodeType = astNodeType;
		this.strValue = value;
		this.range = range;
		this.matched = false;
	}
	
	public boolean isMatched() {
		return matched;
	}	
	
	public void setMatched() {
		matched = true;
	}
	
	public void setUnmatched() {
		matched = false;
	}
	
	public int getNodeType() {
		return astNodeType;
	}
	
	public String getStrValue() {
		return strValue;
	}
	
	public SourceCodeRange getRange() {
		return range;
	}
	
	@Override
	public String toString() {
		return strValue;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + astNodeType;
		result = prime * result + ((range == null) ? 0 : range.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		GeneralNode other = (GeneralNode) obj;
		if (astNodeType != other.astNodeType)
			return false;
		if (range == null) {
			if (other.range != null)
				return false;
		} else if (!range.equals(other.range))
			return false;
		return true;
	}
	
	public boolean isSpecialForMatch() {
		return strValue.equals("then:") || strValue.equals("else:")
				|| strValue.equals("try-body:") || strValue.equals("finally:")
				|| strValue.equals("anonyClass");
	}
	
	public boolean isStructureNode() {
		switch(astNodeType) {
		case ASTNode.METHOD_DECLARATION:
		case ASTNode.ANONYMOUS_CLASS_DECLARATION:
		case ASTNode.CATCH_CLAUSE:
		case ASTNode.DO_STATEMENT:
		case ASTNode.ENHANCED_FOR_STATEMENT:
		case ASTNode.FOR_STATEMENT:
		case ASTNode.IF_STATEMENT:
		case ASTNode.SWITCH_CASE:
		case ASTNode.SWITCH_STATEMENT:
		case ASTNode.SYNCHRONIZED_STATEMENT:
		case ASTNode.TRY_STATEMENT:
		case ASTNode.WHILE_STATEMENT:
			return true;			
		default: if (strValue.equals("then:") || strValue.equals("else:") || 
				strValue.equals("try-body:") || strValue.equals("finally:"))
					return true;
				return false;
		}
	}
	
	@Override
	public Object clone() {
		Object obj = super.clone();
		GeneralNode copy = (GeneralNode)obj;
		copy.astNodeType = this.astNodeType;
		copy.range = this.range;
		copy.strValue = this.strValue;
		copy.matched = this.matched;
		return obj;
	}
	
	public GeneralNode deepCopy() {
		GeneralNode copy = (GeneralNode)this.clone();
		Enumeration<GeneralNode> enumeration = this.breadthFirstEnumeration();
		Map<GeneralNode, GeneralNode> map = new HashMap<GeneralNode, GeneralNode>();
		map.put(this, copy);
		GeneralNode oNode = null, nNode = null;
		GeneralNode oChild = null, nChild = null;
		Enumeration<GeneralNode> children = null;
		while (enumeration.hasMoreElements()) {
			oNode = enumeration.nextElement();
			nNode = map.remove(oNode);
			children = oNode.children();
			while (children.hasMoreElements()) {
				oChild = children.nextElement();
				nChild = (GeneralNode) oChild.clone();
				nNode.add(nChild);
				map.put(oChild, nChild);
			}
		}
		return copy;
	}
	
	public Set<GeneralNode> findUnmatchedNodes() {
		Set<GeneralNode> unmatched = new HashSet<GeneralNode>();
		Enumeration<GeneralNode> enumeration = this.postorderEnumeration();
		GeneralNode tmp = null;
		while (enumeration.hasMoreElements()) {
			tmp = enumeration.nextElement();
			if (!tmp.isMatched()) {
				unmatched.add(tmp);
			}
		}
		return unmatched;
	}
	
	public Set<GeneralNode> getAllNodes() {
		Set<GeneralNode> nodes = new HashSet<GeneralNode>();
		Enumeration<GeneralNode> enumeration = this.postorderEnumeration();
		GeneralNode tmp = null;
		while (enumeration.hasMoreElements()) {
			tmp = enumeration.nextElement();
			nodes.add(tmp);
		}
		return nodes;
	}
	
	public List<GeneralNode> getAllChildren() {
		List<GeneralNode> children = new ArrayList<GeneralNode>();
		Enumeration<GeneralNode> cEnum = this.children();
		while (cEnum.hasMoreElements()) {
			children.add(cEnum.nextElement());
		}
		return children;
	}
	
	public void removeNodes(Set<GeneralNode> nodes) {
		for (GeneralNode n : nodes) {
			n.removeFromParent();
		}
	}
}
