/*******************************************************************************
 * PPA - Partial Program Analysis for Java
 * Copyright (C) 2008 Barthelemy Dagenais
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either 
 * version 3 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this library. If not, see 
 * <http://www.gnu.org/licenses/lgpl-3.0.txt>
 *******************************************************************************/
package ca.mcgill.cs.swevo.ppa.ui;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.AnnotationTypeMemberDeclaration;
import org.eclipse.jdt.core.dom.BodyDeclaration;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.EnumConstantDeclaration;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import ca.mcgill.cs.swevo.ppa.SnippetUtil;

/**
 * <p>
 * ASTVisitor that retrieves a map of all names in a compilation unit along with their binding and
 * whether the name is a declaration (def vs use).
 * </p>
 * 
 * <p>
 * Once the ASTVisitor has run, users can retrieve four properties for each name: the binding
 * (string format), the kind of the name (e.g., type, field, method), if the name was a declaration
 * or a use, and the ASTNode. The four lists have the same length and each name has the same index
 * in the four list.
 * </p>
 * 
 * @deprecated use ca.mcgill.cs.swevo.ppa.util.NameMapVisitor
 * @author Barthelemy Dagenais
 * 
 */
public class NameMapVisitor extends ASTVisitor {

	private List<String> bindings = new ArrayList<String>();
	private List<String> bindingsType = new ArrayList<String>();
	private List<Boolean> declarations = new ArrayList<Boolean>();
	private List<ASTNode> nodes = new ArrayList<ASTNode>();
	private boolean filterUnknown = false;
	private boolean encoded = true;
	private boolean augmented = false;

	public final static String METHOD_TYPE = "method";
	public final static String FIELD_TYPE = "field";
	public final static String TYPE_TYPE = "type";

	public NameMapVisitor() {
		super();
	}

	public NameMapVisitor(boolean encoded, boolean filterUnknown) {
		super();
		this.filterUnknown = filterUnknown;
		this.encoded = encoded;
	}

	/**
	 * 
	 * @param encoded
	 *            if True, the string representing the binding will be in the form of a SemDiff
	 *            handle.
	 * @param augmented
	 *            if True, the binding will be augmented with additional type information (e.g., if
	 *            a type is an annotation).
	 * @param filterUnknown
	 *            if True, unknown members and snippet members introduced by PPA are filtered out.
	 */
	public NameMapVisitor(boolean encoded, boolean augmented, boolean filterUnknown) {
		super();
		this.filterUnknown = filterUnknown;
		this.encoded = encoded;
		this.augmented = augmented;
	}
	
	@Override
	public void postVisit(ASTNode node) {
		super.postVisit(node);

		if (node instanceof Expression) {
			Expression exp = (Expression) node;
			// XXX Unfortunately, looking for both name and mi and ci will
			// result in duplicate.
			// This is not a problem since we use a set, but for a true
			// estimation of the number of
			// types used,
			// Another strategy should be used...
			IBinding binding = null;
			if (exp instanceof SimpleName) {
				// In a constructor call, this adds the type, not the "method".
				SimpleName name = (SimpleName) exp;
				binding = name.resolveBinding();
				addBindingText(binding, name, isDeclaration(name));
			} else if (exp instanceof ClassInstanceCreation) {
				// This adds the "constructor"
				ClassInstanceCreation cic = (ClassInstanceCreation) exp;
				binding = cic.resolveConstructorBinding();
				addBindingText(binding, cic, false);
			} else {
				return;
			}

		} else if (node instanceof SuperConstructorInvocation) {
			IBinding binding = null;
			SuperConstructorInvocation sci = (SuperConstructorInvocation) node;
			binding = sci.resolveConstructorBinding();
			addBindingText(binding, sci, false);
		} else if (node instanceof ConstructorInvocation) {
			IBinding binding = null;
			ConstructorInvocation ci = (ConstructorInvocation) node;
			binding = ci.resolveConstructorBinding();
			addBindingText(binding, ci, false);
		}
	}

	private String addBindingText(IBinding binding, ASTNode node, boolean isDeclaration) {
		String bindingText = "";
		if (binding != null) {
			if (binding instanceof IMethodBinding) {
				IMethodBinding mBinding = (IMethodBinding) binding;
				String methodName = mBinding.getName();
				if (!filterUnknown || methodName == null
						|| !methodName.equals(SnippetUtil.SNIPPET_METHOD)) {
					if (encoded) {
						bindingText = ASTUtil.getHandle(binding, augmented);
					} else {
						bindingText = PPABindingsUtil.getFullMethodSignature(mBinding);

					}
					bindings.add(bindingText);
					bindingsType.add(METHOD_TYPE);
					declarations.add(isDeclaration);
					nodes.add(node);
				}
			} else if (binding instanceof IVariableBinding) {
				IVariableBinding vBinding = (IVariableBinding) binding;
				if (vBinding.isField()) {
					if (encoded) {
						bindingText = ASTUtil.getHandle(binding, augmented);
					} else {
						String type = "nil";
						if (vBinding.getType() != null) {
							type = PPABindingsUtil.getTypeString(vBinding.getType());
						}

						String decType = "nil";
						if (vBinding.getDeclaringClass() != null) {
							decType = PPABindingsUtil.getTypeString(vBinding.getDeclaringClass());
						}
						bindingText = type + " " + decType + ":" + vBinding.getName();
					}
					bindings.add(bindingText);
					bindingsType.add(FIELD_TYPE);
					declarations.add(isDeclaration);
					nodes.add(node);
				}
			} else if (binding instanceof ITypeBinding) {
				ITypeBinding typeBinding = (ITypeBinding) binding;
				bindingText = typeBinding.getName();
				// TODO Change SNIPPET FOR SOMETHING THAT WON't BREAK ANYTHING
				// AND HANDLE
				// SUPERSNIPPET!!!
				if (!filterUnknown
						|| (!bindingText.contains(PPATypeRegistry.UNKNWON_CLASS)
								&& !bindingText.contains(SnippetUtil.SNIPPET_CLASS) && !bindingText
								.contains(SnippetUtil.SNIPPET_SUPER_CLASS))) {
					if (encoded) {
						bindingText = ASTUtil.getHandle(binding, augmented);
					}
					bindings.add(bindingText);
					bindingsType.add(TYPE_TYPE);
					declarations.add(isDeclaration);
					nodes.add(node);
				}
			}
		}
		return bindingText;
	}

	/**
	 * 
	 * @return A list of bindings in string format. A binding can be in the form of a SemDiff handle
	 *         or in human-readable form.
	 */
	public List<String> getBindings() {
		return bindings;
	}

	/**
	 * 
	 * @return A list of binding types (e.g., a type, a field, a method). This is a human readable
	 *         form.
	 */
	public List<String> getBindingsType() {
		return bindingsType;
	}

	/**
	 * 
	 * @return A list of booleans indicating whether an expression was a declaration (True) or a
	 *         usage (False).
	 */
	public List<Boolean> getDeclarations() {
		return declarations;
	}

	/**
	 * 
	 * @return The astnode of the expression.
	 */
	public List<ASTNode> getNodes() {
		return nodes;
	}

	public void print() {
		int size = bindings.size();
		for (int i = 0; i < size; i++) {
			System.out.println(bindings.get(i) + " --- " + bindingsType.get(i) + " --- "
					+ declarations.get(i));
		}
	}

	private ASTNode getDeclarationParent(ASTNode node) {
		if (node == null) {
			return null;
		} else if (node instanceof BodyDeclaration) {
			return node;
		} else if (node instanceof VariableDeclaration) {
			return node;
		} else {
			return node.getParent();
		}
	}

	private boolean isDeclaration(SimpleName name) {
		boolean isDeclaration = false;

		ASTNode declaration = getDeclarationParent(name.getParent());

		if (declaration != null) {
			if (declaration instanceof AbstractTypeDeclaration) {
				isDeclaration = name == ((AbstractTypeDeclaration) declaration).getName();
			} else if (declaration instanceof MethodDeclaration) {
				isDeclaration = name == ((MethodDeclaration) declaration).getName();
			} else if (declaration instanceof EnumConstantDeclaration) {
				isDeclaration = name == ((EnumConstantDeclaration) declaration).getName();
			} else if (declaration instanceof AnnotationTypeMemberDeclaration) {
				isDeclaration = name == ((AnnotationTypeMemberDeclaration) declaration).getName();
			} else if (declaration instanceof VariableDeclarationFragment) {
				// Covers FieldDeclaration too!
				isDeclaration = name == ((VariableDeclarationFragment) declaration).getName();
			} else if (declaration instanceof SingleVariableDeclaration) {
				isDeclaration = name == ((SingleVariableDeclaration) declaration).getName();
			}
		}

		return isDeclaration;
	}

}
