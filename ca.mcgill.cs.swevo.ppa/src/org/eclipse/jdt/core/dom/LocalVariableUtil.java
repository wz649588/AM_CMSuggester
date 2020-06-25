package org.eclipse.jdt.core.dom;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Checking whether a ASTNode is a local variable
 * @author Ye Wang
 * @since 02/09/2018
 *
 */
public class LocalVariableUtil {
	
	/**
	 * Check if the node is a local variable (including parameters)
	 * @param node
	 * @return true if the node is a local variable
	 */
	public static boolean isLocalVariable(SimpleName node) {
		LocalVariableUtil instance = new LocalVariableUtil(node);
		return instance.internalCheck();
	}
	
	private SimpleName node;
	
	private LocalVariableUtil(SimpleName node) {
		this.node = node;
	}
	
	private boolean internalCheck() {
		
		if (node == null) {
			System.err.println("LocalVariableUtil.isLocalVariable(SimpleName) gets null node");
			throw new IllegalArgumentException("Node is null");
		}
		
		// If the node is the Name of a QualifiedName, like bar in foo.bar,
		// this node is not a local variable or a parameter
		if (node.getParent() instanceof QualifiedName) {
			QualifiedName qualifiedName = (QualifiedName) node.getParent();
			SimpleName nameOfQualifiedName = qualifiedName.getName();
			if (node == nameOfQualifiedName)
				return false;
		}
		
		// bar in foo.bar or this.bar is not local variable
		if (node.getParent() instanceof FieldAccess) {
			FieldAccess fieldAccess = (FieldAccess) node.getParent();
			SimpleName nameOfFieldAccess = fieldAccess.getName();
			if (node == nameOfFieldAccess)
				return false;
		}
		
		// name in super.name is not local variable
		if (node.getParent() instanceof SuperFieldAccess) {
			SuperFieldAccess superFieldAccess = (SuperFieldAccess) node.getParent();
			SimpleName nameOfSuperFieldAccess = superFieldAccess.getName();
			if (node == nameOfSuperFieldAccess)
				return false;
		}
		
		// qualifier in qualifier.this is not local variable
		if (node.getParent() instanceof ThisExpression) {
			ThisExpression thisExpression = (ThisExpression) node.getParent();
			Name qualifier = thisExpression.getQualifier();
			if (qualifier == node)
				return false;
		}
		
		/*
		 * Get the direct enclosing MethodDeclaration or Initializer
		 */
		ASTNode enclosingNode = node;
		boolean directEnclosingEntityFound = false;
		while (enclosingNode != null && !directEnclosingEntityFound) {
			enclosingNode = enclosingNode.getParent();
			if (enclosingNode instanceof MethodDeclaration
					|| enclosingNode instanceof Initializer)
				directEnclosingEntityFound = true;
		}
		
		// in this case, the SimpleName is not in any type declaration.
		// It is quite possible that it is a package name.
		if (enclosingNode == null) {
			return false;
		}
		
		enclosingMethodList.add(enclosingNode);
		methodToEndpoint.put(enclosingNode, node);
		
		/*
		 *  Check whether the method is in a local class or an anonymous class.
		 *  If yes, it's necessary to get the outermost method whose declaring class
		 *  is not a local class or an anonymous class.
		 */
		boolean anotherEnclosingMethodAdded;
		do {
			anotherEnclosingMethodAdded =
					handleMethodOrInitializerWithUnwantedEnclosingType(enclosingMethodList.getLast());
		} while (anotherEnclosingMethodAdded);
		
		
		
		/*
		 * If the direct enclosing entity is an AbstractTypeDeclaration or
		 * an AnonymousClassDeclaration, this node is not a local variable
		 * or a parameter. If the direct enclosing entity is a MethodDeclaration
		 * or an Initializer, this node may be a local variable or a parameter and may not.
		 */
		if (enclosingNode instanceof AbstractTypeDeclaration
				|| enclosingNode instanceof AnonymousClassDeclaration)
			return false;
		
		// From here, the enclosing node should be either a MethodDeclaration or an Initializer
		
		
		
		for (ASTNode processingNode: enclosingMethodList) {
			// Get effective scopes.
			List<ASTNode> effectiveScopes = new ArrayList<>();
			ASTNode endpoint = methodToEndpoint.get(processingNode);
			ASTNode currentNode = endpoint;
			while (currentNode != processingNode) {
				currentNode = currentNode.getParent();
				if (currentNode instanceof Block
						|| currentNode instanceof CatchClause
						|| currentNode instanceof EnhancedForStatement
						|| currentNode instanceof ForStatement
						|| currentNode instanceof MethodDeclaration
						|| currentNode instanceof Initializer
						|| currentNode instanceof SwitchStatement)
					effectiveScopes.add(currentNode);
			}
			
			LocalVariableVisitor visitor = new LocalVariableVisitor(effectiveScopes, endpoint);
			enclosingNode.accept(visitor);
			
			if (visitor.localVariableNames.contains(node.getIdentifier()))
				return true;
		}
		
		return false;
	}
	
	/**
	 * The member should be instances of MethodDeclaration or Initializer
	 */
	private LinkedList<ASTNode> enclosingMethodList = new LinkedList<>();
	
	/**
	 * Key: enclosing method, type of which can be MethodDeclaration or Initializer
	 * Value: visitor's end point, its type can be SimpleName, TypeDeclarationStatement, or AnonymousClassDeclaration
	 * The end point should be a descendant node of enclosing method.
	 */
	private Map<ASTNode, ASTNode> methodToEndpoint = new HashMap<>(); 
	
	/**
	 * if a method or an initializer is in a local class or
	 * an anonymous class inside a method, add the outer enclosing method of
	 * the local class or the anonymous class to list.
	 * @param node a method or an initializer
	 * @return true if an outer enclosing method is added to enclosingMethodList
	 */
	private boolean handleMethodOrInitializerWithUnwantedEnclosingType(ASTNode node) {
		// First get enclosing type
		ASTNode current = getEnclosingType(node);
		if (current == null)
			return false;
		if (current instanceof TypeDeclaration || current instanceof EnumDeclaration) {
			ASTNode parent = current.getParent();
			if (parent instanceof TypeDeclarationStatement) {
				// Get the enclosing method or initializer
				ASTNode result = parent;
				while (result != null) {
					result = result.getParent();
					if (result instanceof MethodDeclaration || result instanceof Initializer)
						break;
				}
				// Add the enclosing entity to list
				if (result != null) {
					enclosingMethodList.add(result);
					methodToEndpoint.put(result, parent);
					return true;
				} else {
					return false;
				}
			} else
				return false;
		} else if (current instanceof AnonymousClassDeclaration) {
			// Get the enclosing class or method. If it's a class, return false
			// If it's a method, add the method to list and return true.
			ASTNode result = current;
			while (result != null) {
				result = result.getParent();
				if (result instanceof AbstractTypeDeclaration
						|| result instanceof AnonymousClassDeclaration
						|| result instanceof MethodDeclaration
						|| result instanceof Initializer)
					break;
			}
			if (result instanceof MethodDeclaration || result instanceof Initializer) {
				enclosingMethodList.add(result);
				methodToEndpoint.put(result, current);
				return true;
			} else {
				return false;
			}
			
		}
		
		return false;
	}
	
	/**
	 * Get enclosing type of the given node. If not found, it should return null.
	 * @param node
	 * @return an instance of AbstractTypeDeclaration or AnonymousClassDeclaration
	 */
	private static ASTNode getEnclosingType(ASTNode node) {
		ASTNode result = node;
		while (result != null) {
			result = result.getParent();
			if (result instanceof AbstractTypeDeclaration
					|| result instanceof AnonymousClassDeclaration)
				break;
		}
		return result;
	}
	
}

class LocalVariableVisitor extends ASTVisitor {
	
	private List<ASTNode> effectiveScopes;
	
	private ASTNode endpoint;
	
	private boolean endpointReached = false;
	
	Set<String> localVariableNames = new HashSet<>();
	
	LocalVariableVisitor(List<ASTNode> effectiveScopes, ASTNode endpoint) {
		this.effectiveScopes = effectiveScopes;
		this.endpoint = endpoint;
	}
	
	@Override
	public boolean visit(Block node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(CatchClause node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(EnhancedForStatement node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(ForStatement node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(Initializer node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(SwitchStatement node) {
		return effectiveScopes.contains(node);
	}
	
	@Override
	public boolean visit(SimpleName node) {
		if (node == endpoint)
			endpointReached = true;
		return false;
	}
	
	@Override
	public boolean visit(TypeDeclarationStatement node) {
		if (node == endpoint)
			endpointReached = true;
		return false;
	}
	
	@Override
	public boolean visit(AnonymousClassDeclaration node) {
		if (node == endpoint)
			endpointReached = true;
		return false;
	}
	
	@Override
	public boolean visit(SingleVariableDeclaration node) {
		if (!endpointReached) 
			localVariableNames.add(node.getName().getIdentifier());
		return super.visit(node);
	}
	
	@Override
	public boolean visit(VariableDeclarationFragment node) {
		if (!endpointReached)
			localVariableNames.add(node.getName().getIdentifier());
		return super.visit(node);
	}
}


