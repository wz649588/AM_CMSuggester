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
package org.eclipse.jdt.core.dom;

import java.util.Arrays;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.DefaultBindingResolver;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.RecoveredTypeBinding;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.AllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.ArrayQualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.ArrayTypeReference;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.ConditionalExpression;
import org.eclipse.jdt.internal.compiler.ast.ExpressionContext;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.ParameterizedSingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ast.PrefixExpression;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.StringLiteralConcatenation;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.MissingTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.PPASourceTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.PPATypeBindingOptions;
import org.eclipse.jdt.internal.compiler.lookup.ParameterizedTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemFieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TagBits;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.VariableBinding;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

public class PPADefaultBindingResolver extends DefaultBindingResolver {

	private PPATypeRegistry typeRegistry;

	private CompilationUnit currentCu;

	public PPADefaultBindingResolver(DefaultBindingResolver resolver,
			PPATypeRegistry typeRegistry) {
		super(resolver.scope(), resolver.workingCopyOwner,
				resolver.bindingTables, resolver.isRecoveringBindings, true);
		this.astNodesToBlockScope = resolver.astNodesToBlockScope;
		this.bindingsToAstNodes = resolver.bindingsToAstNodes;
		this.newAstToOldAst = resolver.newAstToOldAst;
		this.typeRegistry = typeRegistry;
	}



	@SuppressWarnings("unchecked")
	public void fixBinary(ASTNode node, ITypeBinding newType) {
		Object obj = this.newAstToOldAst.get(node); //added by nameng, since obj can be StringLiteralConcatenation
		if (obj instanceof BinaryExpression) {
			BinaryExpression bExpression = (BinaryExpression) this.newAstToOldAst
					.get(node);
			org.eclipse.jdt.core.dom.TypeBinding tBinding = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			bExpression.resolvedType = tBinding.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(tBinding.binding,
					newType);
		} else { //added by nameng for StringLiteralConcatenation
			StringLiteralConcatenation slc = (StringLiteralConcatenation)obj;
			InfixExpression infix = (InfixExpression)node;
			Expression left = infix.getLeftOperand();
			Expression right = infix.getRightOperand();
			ITypeBinding leftBinding = left.resolveTypeBinding();
			ITypeBinding newBinding = null;
			if (leftBinding != null && leftBinding.toString().contains("java.lang.String")) {
				newBinding = leftBinding;
			} else {
				newBinding = right.resolveTypeBinding();
			}
			TypeBinding binding = ((org.eclipse.jdt.core.dom.TypeBinding)newBinding).binding;
			slc.resolvedType = binding;
			this.bindingTables.compilerBindingsToASTBindings.put(binding, newBinding);
		}
	}
	
	
	@SuppressWarnings("unchecked")
	public void fixConditional(ASTNode node, ITypeBinding newType) {
		ConditionalExpression cExpression = (ConditionalExpression) this.newAstToOldAst.get(node);
		org.eclipse.jdt.core.dom.TypeBinding tBinding = (org.eclipse.jdt.core.dom.TypeBinding) newType;
		if(tBinding!=null){
			cExpression.resolvedType = tBinding.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(tBinding.binding,
					newType);
		}
	}

	public void fixClassInstanceCreation(ClassInstanceCreation classInstanceNode) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode astNode = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(classInstanceNode);

		if (astNode instanceof AllocationExpression) {
			AllocationExpression aExp = (AllocationExpression) astNode;
			if (isProblematicBinding(aExp.resolvedType)) {
				if (aExp.type != null) {
					aExp.resolvedType = aExp.type.resolvedType;
					aExp.typeArguments = new TypeReference[0];
				}
			}

			boolean problematic = isProblematicBinding(aExp.binding);

			if ((problematic && aExp.resolvedType instanceof ReferenceBinding)
					|| isObjectBinding(aExp.binding)) {
				
				// added by Ye Wang, 02/06/2018
				if (aExp.resolvedType instanceof ReferenceBinding) {
				// ---	
					
				// ReferenceBinding container = (ReferenceBinding)
				// aExp.resolvedType;
				int number = aExp.arguments != null ? aExp.arguments.length : 0;
				try{
					aExp.binding = typeRegistry
							.getInternalUnknownConstructorBinding(
									(ReferenceBinding) aExp.resolvedType, number,
									this);
				}catch(Exception e){
//					e.printStackTrace();  // added by Ye Wang, for debug
					System.out.println("zhh Error at public void fixClassInstanceCreation(ClassInstanceCreation classInstanceNode)");
					exdist.ExceptionHandler.process(e, "zhh Error at public void fixClassInstanceCreation(ClassInstanceCreation classInstanceNode)");
				}
				
				// added by Ye Wang
				} else if (aExp.type instanceof ParameterizedSingleTypeReference
						&& aExp.resolvedType instanceof ArrayBinding){
					int number = aExp.arguments != null ? aExp.arguments.length : 0;
					ReferenceBinding rBinding = typeRegistry
							.getParameterizedTypeBinding(
									(ReferenceBinding) ((ArrayBinding) aExp.resolvedType)
											.leafComponentType(),
									(ParameterizedSingleTypeReference) aExp.type,
									this);
					aExp.resolvedType = rBinding;
					aExp.binding = typeRegistry
							.getInternalUnknownConstructorBinding(rBinding, number,
									this);
				} else {
					throw new UnsupportedOperationException("yw Error at public void fixClassInstanceCreation(ClassInstanceCreation classInstanceNode)");
				}
				// ---
			}
			// This is the case when instantiating a Generic with unknown
			// component types
			else if (problematic
					&& aExp.type instanceof ParameterizedSingleTypeReference
					&& aExp.resolvedType instanceof ArrayBinding) {
				int number = aExp.arguments != null ? aExp.arguments.length : 0;
				ReferenceBinding rBinding = typeRegistry
						.getParameterizedTypeBinding(
								(ReferenceBinding) ((ArrayBinding) aExp.resolvedType)
										.leafComponentType(),
								(ParameterizedSingleTypeReference) aExp.type,
								this);
				aExp.resolvedType = rBinding;
				aExp.binding = typeRegistry
						.getInternalUnknownConstructorBinding(rBinding, number,
								this);
			}
		} else {
			TypeDeclaration typeDec = (TypeDeclaration) astNode;
			TypeDeclaration parent = (TypeDeclaration) this.newAstToOldAst
					.get(PPAASTUtil.getSpecificParentType(classInstanceNode,
							ASTNode.TYPE_DECLARATION));
			if (isProblematicBinding(typeDec.binding)
					&& typeDec.allocation != null) {
				TypeReference typeRef = typeDec.allocation.type;
				if (typeRef != null
						&& typeRef.resolvedType instanceof ReferenceBinding) {
					ReferenceBinding typeBinding = (ReferenceBinding) typeRef.resolvedType;
					typeDec.allocation.resolvedType = typeBinding;
					typeDec.scope = new ClassScope(parent.scope, typeDec);
					typeDec.binding = new PPASourceTypeBinding(
							typeBinding.compoundName, typeBinding.fPackage,
							typeDec.scope);
					typeDec.binding.sourceName = typeBinding.sourceName;
					typeDec.binding.typeVariables = new TypeVariableBinding[0];
				}

			}

			// The allocation.binding can be problematic even if allocation or
			// binding is not when
			// the ASTParser
			// partially succeeds.
			if (isProblematicBinding(typeDec.allocation.binding)
					&& typeDec.allocation.resolvedType instanceof ReferenceBinding) {
				// ReferenceBinding container = (ReferenceBinding)
				// typeDec.allocation.resolvedType;
				int number = typeDec.allocation.arguments != null ? typeDec.allocation.arguments.length
						: 0;
				typeDec.allocation.binding = typeRegistry
						.getInternalUnknownConstructorBinding(
								(ReferenceBinding) typeDec.allocation.resolvedType,
								number, this);
			}
		}				
	}

	public void fixClassInstanceCreation(
			ClassInstanceCreation classInstanceNode, IMethodBinding mBinding) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode astNode = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(classInstanceNode);

		if (astNode instanceof AllocationExpression) {
			AllocationExpression aExp = (AllocationExpression) astNode;
			if (isProblematicBinding(aExp.resolvedType)) {
				if (aExp.type != null) {
					aExp.resolvedType = aExp.type.resolvedType;
					aExp.typeArguments = new TypeReference[0];
				}
			}

			int number = aExp.arguments != null ? aExp.arguments.length : 0;
			try{
				aExp.binding = typeRegistry.getInternalConstructorBinding(
						(ReferenceBinding) aExp.resolvedType, number,
						mBinding.getParameterTypes(), this);
			}catch(Exception e){
				System.out.println("zhh error at public void fixClassInstanceCreation(");
				exdist.ExceptionHandler.process(e, "zhh error at public void fixClassInstanceCreation(");
			}
		} else if (astNode != null
				&& (astNode.bits & org.eclipse.jdt.internal.compiler.ast.ASTNode.IsAnonymousType) != 0) {
			// XXX Fix the anonymous class creation case
			org.eclipse.jdt.internal.compiler.ast.TypeDeclaration anonExp = (org.eclipse.jdt.internal.compiler.ast.TypeDeclaration) astNode;

			if (isProblematicBinding(anonExp.allocation.resolvedType)) {
				if (anonExp.allocation.type != null) {
					anonExp.allocation.resolvedType = anonExp.allocation.type.resolvedType;
					anonExp.allocation.typeArguments = new TypeReference[0];
				}
			}

			int number = anonExp.allocation.arguments != null ? anonExp.allocation.arguments.length
					: 0;
			anonExp.allocation.binding = typeRegistry
					.getInternalConstructorBinding(
							(ReferenceBinding) anonExp.allocation.resolvedType,
							number, mBinding.getParameterTypes(), this);
		}
	}

	public void fixFieldBinding(Name name, IVariableBinding newFieldBinding) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		
		if(newFieldBinding!=null){
			if (node instanceof SingleNameReference) {
				fixFieldSingleNameBinding((SingleNameReference) node,
						newFieldBinding);
			} else if (node instanceof FieldReference) {
				fixFieldReferenceBinding((FieldReference) node, newFieldBinding);
			} else if (node instanceof QualifiedNameReference) {
				fixQualifiedNameReference(name, (QualifiedNameReference) node,
						newFieldBinding);
			}
			else if(node instanceof org.eclipse.jdt.internal.compiler.ast.FieldDeclaration){
				org.eclipse.jdt.internal.compiler.ast.FieldDeclaration fd = (org.eclipse.jdt.internal.compiler.ast.FieldDeclaration)node;
				fixFieldDeclaration(fd, newFieldBinding);
			}
		}
	}

	private void fixFieldDeclaration(org.eclipse.jdt.internal.compiler.ast.FieldDeclaration fd,
			IVariableBinding newFieldBinding) {
		// TODO Auto-generated method stub
		fd.binding = typeRegistry
				.getInternalFieldBinding(newFieldBinding);
	}



	@SuppressWarnings("unchecked")
	private void fixFieldReferenceBinding(FieldReference fieldRef,
			IVariableBinding newFieldBinding) {
		org.eclipse.jdt.core.dom.TypeBinding typeBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getType();
		org.eclipse.jdt.core.dom.TypeBinding containerBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getDeclaringClass();
		fieldRef.resolvedType = typeBinding.binding;

		// XXX This is the Array length exception (it seems the Eclipse compiler
		// does not give it a container!)
		if (containerBinding == null
				&& newFieldBinding.toString().equals("public final int length")) {
			fieldRef.binding = ArrayBinding.ArrayLength;
		} else if (containerBinding.binding instanceof ReferenceBinding) {
			fieldRef.binding = typeRegistry
					.getInternalFieldBinding(newFieldBinding);
		}
		
		this.bindingTables.compilerBindingsToASTBindings.put(fieldRef.binding,
				newFieldBinding);
	}

	@SuppressWarnings("unchecked")
	private void fixFieldSingleNameBinding(
			SingleNameReference singleNameReference,
			IVariableBinding newFieldBinding) {
		org.eclipse.jdt.core.dom.TypeBinding typeBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getType();
		org.eclipse.jdt.core.dom.TypeBinding containerBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getDeclaringClass();
		singleNameReference.resolvedType = typeBinding.binding;

		// XXX This is the Array length exception (does not have a container!)
		if (containerBinding == null
				&& newFieldBinding.toString().equals("public final int length")) {
			singleNameReference.binding = ArrayBinding.ArrayLength;
		} else if (containerBinding.binding instanceof ReferenceBinding) {
			singleNameReference.binding = typeRegistry
					.getInternalFieldBinding(newFieldBinding);
			singleNameReference.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																											// bits
			singleNameReference.bits |= Binding.FIELD;
		}
		this.bindingTables.compilerBindingsToASTBindings.put(
				singleNameReference.binding, newFieldBinding);

	}

	@SuppressWarnings("unchecked")
	public void fixFQNField(ASTNode node, IVariableBinding newFieldBinding,
			String current, boolean lastOfItsKind) {
		QualifiedNameReference qReference = (QualifiedNameReference) this.newAstToOldAst
				.get(node);
		org.eclipse.jdt.core.dom.TypeBinding typeBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getType();
		org.eclipse.jdt.core.dom.TypeBinding containerBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getDeclaringClass();

		if (lastOfItsKind) {
			qReference.resolvedType = typeBinding.binding;
		}

		// XXX This is the Array length exception (does not have a container!)
		FieldBinding internalBinding = null;
		if (containerBinding == null
				&& newFieldBinding.toString().equals("public final int length")) {
			internalBinding = ArrayBinding.ArrayLength;
		} else {
			internalBinding = typeRegistry
					.getInternalFieldBinding(newFieldBinding);
		}

		if (internalBinding != null || containerBinding != null
				&& containerBinding.binding instanceof ReferenceBinding) {
			if (qReference.binding == null
					|| qReference.binding instanceof ProblemBinding
					|| qReference.binding instanceof ProblemFieldBinding) {
				qReference.binding = internalBinding;
//				qReference.indexOfFirstFieldBinding = current.split("\\.").length;//commented out by nameng
				int length = qReference.otherBindings != null ? qReference.otherBindings.length
						: 0;
				int index = length;
				if (node instanceof Name) {
					Name name = (Name) node;
					if (name.index == qReference.indexOfFirstFieldBinding) {
						// Everything before that is known.
						index = name.index;
					} else {
						index = name.index
								- qReference.indexOfFirstFieldBinding - 1;
					}
				}

				FieldBinding[] newOthers = qReference.otherBindings;

				if (index > length - 1) {
					newOthers = new FieldBinding[index + 1];
					if (length > 0) {
						System.arraycopy(qReference.otherBindings, 0,
								newOthers, 0, length);
					}
				}
				
				newOthers[index] = internalBinding;
				qReference.otherBindings = newOthers;
				
				this.bindingTables.compilerBindingsToASTBindings.put(
						qReference.binding, newFieldBinding);
			} else if (isLocalVariable(node, qReference.binding)) {
				qReference.indexOfFirstFieldBinding = 1;
			} else {
				int length = qReference.otherBindings != null ? qReference.otherBindings.length
						: 0;
				int index = length;

				if (node instanceof Name) {
					Name name = (Name) node;
					if (name.index == qReference.indexOfFirstFieldBinding) {
						// Everything before that is known.
						index = name.index;
					} else {
						index = name.index
								- qReference.indexOfFirstFieldBinding - 1;
					}
				}

				FieldBinding[] newOthers = qReference.otherBindings;
				
				if (index > length - 1) {
//				if (index == length || (index != length - 1)) { // commented out by nameng
					newOthers = new FieldBinding[index + 1];
					if (length > 0) {
						System.arraycopy(qReference.otherBindings, 0,
								newOthers, 0, length);
					}
				}
				// else if () {
				// // This means that everything before this was a type (not a
				// local variable)
				// newOthers = new FieldBinding[length + 1];
				// if (length > 0) {
				// System.arraycopy(qReference.otherBindings, 0, newOthers, 0,
				// length);
				// }
				//
				// }
//				if (index < newOthers.length) {//commented out by nameng
					newOthers[index] = internalBinding;
//				} else {
//					// XXX This is to fix a strange PPA error in SemDiff...
//					newOthers[newOthers.length - 1] = internalBinding;
//				}
				qReference.otherBindings = newOthers;
			}
		}
	}

	@SuppressWarnings("unchecked")
	public void fixFQNType(ASTNode name, String fqn) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);

		QualifiedNameReference qRef = (QualifiedNameReference) node;
		PPATypeBindingOptions options = new PPATypeBindingOptions();
		if (name instanceof Name) {
			options = PPATypeBindingOptions.parseOptions((Name) name);
		}

		ITypeBinding binding = typeRegistry.getTypeBinding(
				(CompilationUnit) PPAASTUtil.getSpecificParentType(name,
						ASTNode.COMPILATION_UNIT), fqn, this, false, options);
		org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) binding;
		qRef.resolvedType = itb.binding;
		qRef.binding = itb.binding;
		qRef.indexOfFirstFieldBinding = qRef.tokens.length;
		this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
				binding);
	}

//	public void fixContainerType(ASTNode container, ITypeBinding typeB) {
//		// TODO Auto-generated method stub
//		QualifiedNameReference snr = (QualifiedNameReference)container;
//	}
	@SuppressWarnings("unchecked")
	public void fixLocal(Name name) {
		IBinding binding = super.resolveName(name);
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		if (!(node instanceof LocalDeclaration))  // added by Ye Wang, fix a bug, 02/11/2018
			return;
		if (binding == null || binding instanceof RecoveredTypeBinding) {
			LocalDeclaration ld = (LocalDeclaration) node;
			if(ld.type!=null){
				if(ld.type.resolvedType==null){
					String typeName = ld.type.toString();
					if(typeName.compareTo("boolean")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 5);
					}else if(typeName.compareTo("byte")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 3);
					}else if(typeName.compareTo("char")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 2);
					}else if(typeName.compareTo("short")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 4);
					}else if(typeName.compareTo("double")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 8);
					}else if(typeName.compareTo("float")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 9);
					}else if(typeName.compareTo("int")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 10);
					}else if(typeName.compareTo("long")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 7);
					}else if(typeName.compareTo("string")==0){
						ld.type.resolvedType =  TypeBinding.wellKnownType(this.scope(), 11);
					}else{
						ld.type.resolvedType = this.scope().getType(typeName.toCharArray());
					}
					
				}
				if (ld.binding != null) {
					ld.binding.type = ld.type.resolvedType;
				} else {
					ld.binding = new LocalVariableBinding(ld.name,
							ld.type.resolvedType, ld.modifiers,
							ld.getKind() == LocalDeclaration.PARAMETER);
					ld.binding.type = ld.type.resolvedType;
				}
				
				binding = new org.eclipse.jdt.core.dom.VariableBinding(this,
						ld.binding);
				this.bindingTables.compilerBindingsToASTBindings.put(ld.binding,
						binding);
			}
		}
	}

	@SuppressWarnings("unchecked")
	public void fixMessageSend(Name name) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		MessageSend mSend = (MessageSend) node;
		MethodBinding oldBinding = mSend.binding;
		MethodBinding newBinding = null;
		// org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding container =
		// null;
		// ITypeBinding potentialContainer = getPotentialContainer(name);

		if (oldBinding != null) {
			// params = oldBinding.parameters;
			// if (params == null) {
			// params = new
			// org.eclipse.jdt.internal.compiler.lookup.TypeBinding[0];
			// }
			// container = oldBinding.declaringClass;
			// if (container == null || PPAUtil.isUnknownType(container)) {
			// if (potentialContainer != null
			// && potentialContainer instanceof
			// org.eclipse.jdt.core.dom.TypeBinding) {
			// container =
			// (org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding)
			// ((org.eclipse.jdt.core.dom.TypeBinding)
			// potentialContainer).binding;
			// }
			// }
			// newBinding =
			// typeRegistry.createMethodBinding(oldBinding.selector, container,
			// oldBinding.returnType, params, this);
			//
			int number = oldBinding.parameters != null ? oldBinding.parameters.length
					: 0;
			newBinding = typeRegistry.getInternalUnknownMethodBinding(
					oldBinding.selector, number, this);
		} else {
			// if (mSend.arguments == null) {
			// params = new
			// org.eclipse.jdt.internal.compiler.lookup.TypeBinding[0];
			// } else {
			// params = new
			// org.eclipse.jdt.internal.compiler.lookup.TypeBinding[mSend.
			// arguments.length];
			// }
			// if (potentialContainer != null
			// && potentialContainer instanceof
			// org.eclipse.jdt.core.dom.TypeBinding) {
			// container =
			// (org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding)
			// ((org.eclipse.jdt.core.dom.TypeBinding)
			// potentialContainer).binding;
			// }
			// newBinding = typeRegistry.createMethodBinding(mSend.selector,
			// container, null,
			// params,
			// this);
			int number = mSend.arguments != null ? mSend.arguments.length : 0;
			newBinding = typeRegistry.getInternalUnknownMethodBinding(
					mSend.selector, number, this);
		}

		mSend.binding = newBinding;
		if (mSend.actualReceiverType == null
				|| !newBinding.declaringClass
						.isEquivalentTo(mSend.actualReceiverType)) {
			mSend.actualReceiverType = newBinding.declaringClass;
		}
		mSend.resolvedType = newBinding.returnType;
		this.bindingTables.compilerBindingsToASTBindings.put(newBinding,
				new org.eclipse.jdt.core.dom.MethodBinding(this, newBinding));
	}

	@SuppressWarnings("unchecked")
	public void fixMessageSend(Name name, IMethodBinding newMethodBinding) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		if (node instanceof MessageSend) {
			MessageSend mSend = (MessageSend) node;
			ITypeBinding[] params = newMethodBinding.getParameterTypes();
			int size = params.length;
			TypeBinding[] internalParams = new TypeBinding[size];

			for (int i = 0; i < size; i++) {
				internalParams[i] = PPABindingsUtil
						.getInternalTypeBinding(params[i]);
			}

			MethodBinding newInternalMBinding = new MethodBinding(
					ClassFileConstants.AccPublic, newMethodBinding.getName()
							.toCharArray(),
					PPABindingsUtil.getInternalTypeBinding(newMethodBinding
							.getReturnType()), internalParams,
					new ReferenceBinding[0],
					(ReferenceBinding) PPABindingsUtil
							.getInternalTypeBinding(newMethodBinding
									.getDeclaringClass()));

			mSend.binding = newInternalMBinding;
			mSend.resolvedType = newInternalMBinding.returnType;
			mSend.actualReceiverType = newInternalMBinding.declaringClass;
			this.bindingTables.compilerBindingsToASTBindings.put(
					newInternalMBinding, newMethodBinding);
		}
	}

	public void fixMethodDeclaration(MethodDeclaration node) {
		AbstractMethodDeclaration aMethodDec = (AbstractMethodDeclaration) this.newAstToOldAst
				.get(node);

		MethodBinding mBinding = aMethodDec.binding;

		if (mBinding != null) {

			// First, fix return type
			if (aMethodDec instanceof org.eclipse.jdt.internal.compiler.ast.MethodDeclaration) {
				org.eclipse.jdt.internal.compiler.ast.MethodDeclaration tempDec = (org.eclipse.jdt.internal.compiler.ast.MethodDeclaration) aMethodDec;
				if (tempDec.returnType != null
						&& !isProblematicBinding(tempDec.returnType.resolvedType)
						&& isProblematicBinding(mBinding.returnType)) {
					mBinding.returnType = tempDec.returnType.resolvedType;
				}

			}

			// Then, fix parameters
			if (aMethodDec.arguments != null) {
				for (int index = 0; index < aMethodDec.arguments.length; index++) {
					if (isProblematicBinding(mBinding.parameters[index])
							&& !isProblematicBinding(aMethodDec.arguments[index].binding)) {
						mBinding.parameters[index] = aMethodDec.arguments[index].binding.type;
					}
				}
			}

			// This is to remove the missing type tagbit. I know, it's annoying.
			mBinding.tagBits = (mBinding.tagBits ^ TagBits.HasMissingType);
		}

	}

	@SuppressWarnings("unchecked")
	private void fixQualifiedNameReference(Name name,
			QualifiedNameReference node, IVariableBinding newFieldBinding) {

		int index = name.index;

		org.eclipse.jdt.core.dom.TypeBinding typeBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getType();
		org.eclipse.jdt.core.dom.TypeBinding containerBinding = (org.eclipse.jdt.core.dom.TypeBinding) newFieldBinding
				.getDeclaringClass();

		if (index == node.indexOfFirstFieldBinding) {
			// XXX This is the Array length exception (does not have a
			// container!)
			if (containerBinding == null
					&& newFieldBinding.toString().equals(
							"public final int length")) {
				node.binding = ArrayBinding.ArrayLength;
			} else if (containerBinding.binding instanceof ReferenceBinding) {
				node.binding = typeRegistry
						.getInternalFieldBinding(newFieldBinding);
				node.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																									// bits
				node.bits |= Binding.FIELD;
			}
			this.bindingTables.compilerBindingsToASTBindings.put(node.binding,
					newFieldBinding);
		} else if (index > node.indexOfFirstFieldBinding) {
			// XXX This is the Array length exception (does not have a
			// container!)
			if (containerBinding == null
					&& newFieldBinding.toString().equals(
							"public final int length")) {
				node.otherBindings[index - node.indexOfFirstFieldBinding - 1] = ArrayBinding.ArrayLength;
			} else if (containerBinding.binding instanceof ReferenceBinding) {
				if(node.otherBindings==null){
					node.otherBindings = new FieldBinding[index];
				} 
//				else {//added by nameng: when otherBindings != null, copy the original bindings to the new one					
//					node.otherBindings = Arrays.copyOf(node.otherBindings, index);
//				}
				node.otherBindings[index - node.indexOfFirstFieldBinding - 1] = typeRegistry
						.getInternalFieldBinding(newFieldBinding);
				node.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																									// bits
				node.bits |= Binding.FIELD;
			}
		} else {
			assert false;
		}

		if (node.otherBindings == null
//				|| (index - node.indexOfFirstFieldBinding) == node.otherBindings.length) {
				|| (index - node.indexOfFirstFieldBinding) <= node.otherBindings.length) {
			node.resolvedType = typeBinding.binding;
		}
	}

	@SuppressWarnings("unchecked")
	public void fixQualifiedTypeReference(Name name) {
		IBinding binding = super.resolveName(name);
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);

		if (binding == null || binding instanceof RecoveredTypeBinding) {
			QualifiedTypeReference qRef = (QualifiedTypeReference) node;
			String fullName = PPAASTUtil.getFQNFromAnyName(name);
			binding = typeRegistry.getTypeBinding((CompilationUnit) PPAASTUtil
					.getSpecificParentType(name, ASTNode.COMPILATION_UNIT),
					fullName, this,
					qRef instanceof ArrayQualifiedTypeReference,
					PPATypeBindingOptions.parseOptions(name));

			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) binding;
			qRef.resolvedType = itb.binding;
			qRef.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																								// bits
			qRef.bits |= Binding.TYPE;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					binding);
		}
	}

	@SuppressWarnings("unchecked")
	public void fixSimpleType(SimpleType node) {
		Object internalNode = this.newAstToOldAst.get(node);

		if (internalNode instanceof SingleTypeReference) {
			TypeReference typeR = (TypeReference) internalNode;
			ITypeBinding binding = typeRegistry.getTypeBinding(
					(CompilationUnit) PPAASTUtil.getSpecificParentType(node,
							ASTNode.COMPILATION_UNIT), node.getName()
							.getFullyQualifiedName(), this,
					(typeR instanceof ArrayTypeReference)
							|| (typeR instanceof ArrayQualifiedTypeReference),
					new PPATypeBindingOptions());
			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) binding;
			typeR.resolvedType = itb.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					binding);
		} else if (internalNode instanceof QualifiedTypeReference) {
			// TODO Yes, another qualified type reference to take care of.
		} else {
			// TODO Can also be a single name. To check.
		}
	}

	/**
	 * <p>
	 * Adds a missing binding to an internal AST node representing a
	 * parameterized type, by creating the most probable binding.
	 * </p>
	 * 
	 * @param name
	 */
	public void fixParameterizedSingleTypeRef(Name name) {
		IBinding binding = super.resolveName(name);
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		if (binding == null || binding instanceof RecoveredTypeBinding) {
			SingleTypeReference stref = (SingleTypeReference) node;
			if (stref instanceof ParameterizedSingleTypeReference) {
				// Don't do anything for now!
				binding = typeRegistry.getParameterizedTypeBinding(
						(CompilationUnit) PPAASTUtil.getSpecificParentType(
								name, ASTNode.COMPILATION_UNIT), name
								.getFullyQualifiedName(), this,
						(ParameterizedSingleTypeReference) stref,
						PPATypeBindingOptions.parseOptions(name));
			}
		}
	}

	/**
	 * <p>
	 * Adds a missing binding to an internal AST node by creating the most
	 * probable binding.
	 * </p>
	 * 
	 * @param name
	 */
	@SuppressWarnings("unchecked")
	public void fixSingleTypeRef(Name name) {
		IBinding binding = super.resolveName(name);
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		if (binding == null || binding instanceof RecoveredTypeBinding) {
			SingleTypeReference stref = (SingleTypeReference) node;
			if (stref instanceof ParameterizedSingleTypeReference) {
				// Don't do anything for now!
			} else {
				binding = typeRegistry.getTypeBinding(
						(CompilationUnit) PPAASTUtil.getSpecificParentType(
								name, ASTNode.COMPILATION_UNIT), name
								.getFullyQualifiedName(), this,
						(node instanceof ArrayTypeReference),
						PPATypeBindingOptions.parseOptions(name));
			}
			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) binding;
			stref.resolvedType = itb.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					binding);
		}
	}

	@SuppressWarnings("unchecked")
	public void fixTypeBinding(Name name, ITypeBinding newTypeBinding) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		if((node instanceof SingleNameReference)){
			SingleNameReference singleNameReference = (SingleNameReference) node;
			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) newTypeBinding;
			singleNameReference.resolvedType = itb.binding;
			singleNameReference.binding = itb.binding;
			singleNameReference.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																											// bits
			singleNameReference.bits |= Binding.TYPE;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					newTypeBinding);
		}else if(node instanceof SingleTypeReference){
			 SingleTypeReference stref = (SingleTypeReference) node;
			 org.eclipse.jdt.core.dom.TypeBinding itb =
			 (org.eclipse.jdt.core.dom.TypeBinding)
			 newTypeBinding;
			 stref.resolvedType = itb.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
						newTypeBinding);
		}
		
		// .getFullyQualifiedName(), this);
	
	}

	public void fixTypeBinding(Assignment assign, ITypeBinding newType) {
		// TODO Auto-generated method stub
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(assign);

		if(node instanceof CompoundAssignment){
			CompoundAssignment ca = (CompoundAssignment)node;
			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			ca.resolvedType = itb.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					newType);
		}else if(node instanceof org.eclipse.jdt.internal.compiler.ast.Assignment){
			org.eclipse.jdt.internal.compiler.ast.Assignment as = (org.eclipse.jdt.internal.compiler.ast.Assignment)node;
			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			as.resolvedType = itb.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
					newType);
		}
//		if((node instanceof SingleNameReference)){
//			SingleNameReference singleNameReference = (SingleNameReference) node;
//			org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) newTypeBinding;
//			singleNameReference.resolvedType = itb.binding;
//			singleNameReference.binding = itb.binding;
//			singleNameReference.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
//																											// bits
//			singleNameReference.bits |= Binding.TYPE;
//			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
//					newTypeBinding);
//		}else if(node instanceof SingleTypeReference){
//			 SingleTypeReference stref = (SingleTypeReference) node;
//			 org.eclipse.jdt.core.dom.TypeBinding itb =
//			 (org.eclipse.jdt.core.dom.TypeBinding)
//			 newTypeBinding;
//			 stref.resolvedType = itb.binding;
//			this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
//						newTypeBinding);
//		}
	}
	public void fixQualifiedTypeBinding(Name name, ITypeBinding newTypeBinding) {
		// TODO Auto-generated method stub
		org.eclipse.jdt.internal.compiler.ast.ASTNode node = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(name);
		
		QualifiedNameReference singleNameReference = (QualifiedNameReference) node;
//		ExpressionContext exc = singleNameReference.getExpressionContext();
		org.eclipse.jdt.core.dom.TypeBinding itb = (org.eclipse.jdt.core.dom.TypeBinding) newTypeBinding;
		singleNameReference.resolvedType = itb.binding;
		singleNameReference.binding = itb.binding;
		singleNameReference.bits &= ~org.eclipse.jdt.internal.compiler.ast.ASTNode.RestrictiveFlagMASK; // clear
																										// bits
		singleNameReference.bits |= Binding.TYPE;
		this.bindingTables.compilerBindingsToASTBindings.put(itb.binding,
				newTypeBinding);
	}

	
	@SuppressWarnings("unchecked")
	public void fixUnary(ASTNode node, ITypeBinding newType) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode aNode = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(node);

		if (aNode instanceof PrefixExpression) {
			PrefixExpression bExpression = (PrefixExpression) aNode;
			org.eclipse.jdt.core.dom.TypeBinding tBinding = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			bExpression.resolvedType = tBinding.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(
					tBinding.binding, newType);
		} else if (aNode instanceof PostfixExpression) {
			PostfixExpression bExpression = (PostfixExpression) aNode;
			org.eclipse.jdt.core.dom.TypeBinding tBinding = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			bExpression.resolvedType = tBinding.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(
					tBinding.binding, newType);
		} else if (aNode instanceof UnaryExpression) {
			UnaryExpression bExpression = (UnaryExpression) aNode;
			org.eclipse.jdt.core.dom.TypeBinding tBinding = (org.eclipse.jdt.core.dom.TypeBinding) newType;
			bExpression.resolvedType = tBinding.binding;
			this.bindingTables.compilerBindingsToASTBindings.put(
					tBinding.binding, newType);
		} 
	}

	public CompilationUnit getCurrentCu() {
		return currentCu;
	}

	@Override
	@SuppressWarnings("unchecked")
	synchronized IMethodBinding getMethodBinding(
			org.eclipse.jdt.internal.compiler.lookup.MethodBinding methodBinding) {
		IMethodBinding mBinding = super.getMethodBinding(methodBinding);

		if (mBinding == null && methodBinding != null
				&& methodBinding.isValidBinding()) {
			// XXX Usually, there is a check to see if there is a missing type:
			// here, we
			// do not want to perform this check because there might be some
			// missing type
			// anyway.
			IMethodBinding binding = (IMethodBinding) this.bindingTables.compilerBindingsToASTBindings
					.get(methodBinding);
			if (binding != null) {
				return binding;
			}
			binding = new org.eclipse.jdt.core.dom.MethodBinding(this,
					methodBinding);
			this.bindingTables.compilerBindingsToASTBindings.put(methodBinding,
					binding);
			return binding;
		}
		return mBinding;
	}

	// For debugging purpose.
	public String getNodeClass(Name name) {
		Object obj = this.newAstToOldAst.get(name);
		return obj.getClass().toString();
	}

	@Override
	@SuppressWarnings("unchecked")
	synchronized ITypeBinding getTypeBinding(TypeBinding referenceBinding) {
		ITypeBinding typeBinding = super.getTypeBinding(referenceBinding);

		if (typeBinding == null
				&& referenceBinding instanceof MissingTypeBinding) {
			MissingTypeBinding mType = (MissingTypeBinding) referenceBinding;
			// XXX We expect that most of the missing types will be uncovered
			// during syntax
			// heuristics pass, which is done once per cu (so current cu is
			// always available even
			// when
			// ppa is performed on multiple files).
			typeBinding = typeRegistry.getTypeBinding(
					currentCu,
					new String(CharOperation
							.concatWith(mType.compoundName, '.')),
					this,
					false,
					new PPATypeBindingOptions(referenceBinding
							.isAnnotationType()));
			this.bindingTables.compilerBindingsToASTBindings.put(
					referenceBinding, typeBinding);
		} else if (typeBinding == null
				&& referenceBinding instanceof ParameterizedTypeBinding) {
			ParameterizedTypeBinding paramType = (ParameterizedTypeBinding) referenceBinding;
			if ((paramType.tagBits & TagBits.HasMissingType) != 0) {
				paramType.tagBits = (paramType.tagBits ^ TagBits.HasMissingType);
			}
			typeBinding = new org.eclipse.jdt.core.dom.TypeBinding(this,
					paramType);
			this.bindingTables.compilerBindingsToASTBindings.put(
					referenceBinding, typeBinding);
		} else if (typeBinding == null
				&& referenceBinding instanceof ArrayBinding) {
			ArrayBinding aBinding = (ArrayBinding) referenceBinding;
			if ((aBinding.tagBits & TagBits.HasMissingType) != 0) {
				aBinding.tagBits = (aBinding.tagBits ^ TagBits.HasMissingType);
			}
			typeBinding = new org.eclipse.jdt.core.dom.TypeBinding(this,
					aBinding);
			this.bindingTables.compilerBindingsToASTBindings.put(
					referenceBinding, typeBinding);
		} else if (typeBinding != null
				&& typeBinding instanceof org.eclipse.jdt.core.dom.TypeBinding) {
			// XXX This is to ensure that this typeBinding is associated to the
			// PPADefaultBindingResolver.
			org.eclipse.jdt.core.dom.TypeBinding newTypeBinding = (org.eclipse.jdt.core.dom.TypeBinding) typeBinding;
			// newTypeBinding.binding.tagBits = (newTypeBinding.binding.tagBits
			// ^
			// TagBits.HasMissingType);
			typeBinding = new org.eclipse.jdt.core.dom.TypeBinding(this,
					newTypeBinding.binding);
			this.bindingTables.compilerBindingsToASTBindings.put(
					referenceBinding, typeBinding);
		}

		return typeBinding;
	}

	public PPATypeRegistry getTypeRegistry() {
		return typeRegistry;
	}

	@Override
	@SuppressWarnings("unchecked")
	synchronized IVariableBinding getVariableBinding(
			VariableBinding variableBinding) {
		IVariableBinding varBinding = super.getVariableBinding(variableBinding);

		if (varBinding == null && variableBinding != null) {
			if (variableBinding.isValidBinding()) {
				org.eclipse.jdt.internal.compiler.lookup.TypeBinding variableType = variableBinding.type;
				if (variableType != null) {
					// XXX Usually, there is a check to see if there is a
					// missing type: here, we
					// do not want to perform this check because there might be
					// some missing type
					// anyway.
					IVariableBinding binding = (IVariableBinding) this.bindingTables.compilerBindingsToASTBindings
							.get(variableBinding);
					if (binding != null) {
						return binding;
					}
					binding = new org.eclipse.jdt.core.dom.VariableBinding(
							this, variableBinding);
					this.bindingTables.compilerBindingsToASTBindings.put(
							variableBinding, binding);
					return binding;
				}
			}
		}

		return varBinding;
	}

	public boolean isFieldReference(Name name) {
		return this.newAstToOldAst.get(name) instanceof FieldReference;
	}

	// private ITypeBinding getPotentialContainer(Name name) {
	// ITypeBinding potentialContainer = null;
	// ASTNode parent = name.getParent();
	// if (parent instanceof MethodInvocation) {
	// MethodInvocation mInvocation = (MethodInvocation) parent;
	// Expression exp = mInvocation.getExpression();
	// if (exp != null) {
	// potentialContainer = exp.resolveTypeBinding();
	// }
	// }
	//
	// return potentialContainer;
	// }

	public boolean isLocalDeclaration(Name name) {
		return this.newAstToOldAst.get(name) instanceof LocalDeclaration;
	}

	private boolean isLocalVariable(ASTNode node, Binding binding) {
		boolean local = false;
		if (node instanceof Name) {
			Name name = (Name) node;
			local = name.index == 1 && binding != null
					&& binding instanceof VariableBinding;
		}

		return local;
	}

	public boolean isMessageSend(Name name) {
		return this.newAstToOldAst.get(name) instanceof MessageSend;
	}

	private boolean isObjectBinding(MethodBinding binding) {
		boolean isObjectBinding = binding != null
				&& new String(binding.declaringClass.sourceName())
						.equals("Object");
		isObjectBinding = isObjectBinding && binding.parameters.length == 0;
		isObjectBinding = isObjectBinding && binding.isConstructor();
		return isObjectBinding;
	}

	public boolean isProblematicBinding(Binding internalBinding) {
		boolean isProblematic = internalBinding == null
				|| !internalBinding.isValidBinding();

		if (!isProblematic && (internalBinding instanceof MethodBinding)) {
			MethodBinding mBinding = (MethodBinding) internalBinding;
			isProblematic = (mBinding.tagBits & TagBits.HasMissingType) != 0;
		} else if (!isProblematic
				&& (internalBinding instanceof org.eclipse.jdt.internal.compiler.lookup.VariableBinding)) {
			org.eclipse.jdt.internal.compiler.lookup.VariableBinding vBinding = (org.eclipse.jdt.internal.compiler.lookup.VariableBinding) internalBinding;
			isProblematic = (vBinding.tagBits & TagBits.HasMissingType) != 0;
		}

		return isProblematic;
	}

	public boolean isProblematicBinding(ClassInstanceCreation node) {
		org.eclipse.jdt.internal.compiler.ast.ASTNode astNode = (org.eclipse.jdt.internal.compiler.ast.ASTNode) this.newAstToOldAst
				.get(node);
		boolean isProblematic = false;
		if (astNode instanceof AllocationExpression) {
			AllocationExpression aExp = (AllocationExpression) astNode;
			isProblematic = isProblematicBinding(aExp.resolvedType)
					|| isProblematicBinding(aExp.binding);
		} else {
			TypeDeclaration typeDec = (TypeDeclaration) astNode;
			isProblematic = isProblematicBinding(typeDec.binding)
					|| (typeDec.allocation != null && (isProblematicBinding(typeDec.allocation.binding) || isProblematicBinding(typeDec.allocation.resolvedType)));
		}

		return isProblematic;
	}

	boolean isProblematicBinding(IBinding binding) {
		boolean isMissingTag = false;

		if (binding instanceof IVariableBinding) {
			IVariableBinding varBinding = (IVariableBinding) binding;
			ITypeBinding typeBinding = varBinding.getType();
			isMissingTag = PPABindingsUtil.isProblemType(typeBinding);
		}

		return isMissingTag;
	}

	public boolean isProblematicBinding(MethodDeclaration node) {
		AbstractMethodDeclaration aMethodDec = (AbstractMethodDeclaration) this.newAstToOldAst
				.get(node);

		return isProblematicBinding(aMethodDec.binding);
	}

	public boolean isProblematicBinding(Name name) {
		boolean isProblematic = false;
		try {
			IBinding binding = super.resolveName(name);
			isProblematic = binding == null || binding instanceof ProblemBinding
					|| isProblematicBinding(binding);
			if(!isProblematic){
			   if(binding instanceof IVariableBinding){
				   	IVariableBinding varB = (IVariableBinding)binding;
				   	if(varB.getDeclaringClass()==null||!varB.getDeclaringClass().isFromSource()){
				   			isProblematic = (binding.getModifiers() & Modifier.PRIVATE) != 0; 			
				   	}

			   }else if(binding instanceof IMethodBinding){
				    IMethodBinding methodB = (IMethodBinding)binding;
				 	if(methodB.getDeclaringClass()==null||!methodB.getDeclaringClass().isFromSource()){
			   			isProblematic = (binding.getModifiers() & Modifier.PRIVATE) != 0;
			   	}
			   }
			}
		} catch (Exception e) {
			isProblematic = true;
		}		
		return isProblematic;
	}

	public boolean isProblematicBinding(SimpleType node) {
		Object internalNode = this.newAstToOldAst.get(node);
		boolean isProblematic = false;
		if (internalNode instanceof TypeReference) {
			TypeReference typeRef = (TypeReference) this.newAstToOldAst
					.get(node);
			isProblematic = isProblematicBinding(typeRef.resolvedType);
		} else if (internalNode instanceof SingleNameReference) {
			SingleNameReference nameRef = (SingleNameReference) this.newAstToOldAst
					.get(node);
			isProblematic = isProblematicBinding(nameRef.resolvedType);
		}

		return isProblematic;
	}

	public boolean isQualifiedNameReference(Name name) {
		Object ast = this.newAstToOldAst.get(name);
		return ast instanceof QualifiedNameReference;
	}

	public boolean isQualifiedTypeReference(Name name) {
		Object ast = this.newAstToOldAst.get(name);
		return ast instanceof QualifiedTypeReference;
	}

	public boolean isSimpleNameRef(Name name) {
		Object ast = this.newAstToOldAst.get(name);
		return ast instanceof SingleNameReference;
	}

	public boolean isParameterizedSingleTypeRef(Name name) {
		return this.newAstToOldAst.get(name) instanceof ParameterizedSingleTypeReference;
	}

	public boolean isSingleTypeRef(Name name) {
		return this.newAstToOldAst.get(name) instanceof SingleTypeReference;
	}

	@Override
	@SuppressWarnings("unchecked")
	synchronized ITypeBinding resolveExpressionType(Expression expression) {
		ITypeBinding typeBinding = null;
		try{
			typeBinding = super.resolveExpressionType(expression);
			if (typeBinding == null && expression instanceof CastExpression) {
				// Get Type
				CompilationUnit cu = (CompilationUnit) PPAASTUtil
						.getSpecificParentType(expression, ASTNode.COMPILATION_UNIT);
				CastExpression castExp = (CastExpression) expression;
				typeBinding = typeRegistry.getTypeBinding(cu, castExp.getType()
						.toString(), this, false, new PPATypeBindingOptions());
				this.bindingsToAstNodes.put(typeBinding, expression);
				String key = typeBinding.getKey();
				if (key != null) {
					this.bindingTables.bindingKeysToBindings.put(key, typeBinding);
				}
	
				// Fix for future use
				org.eclipse.jdt.internal.compiler.ast.Expression compilerExpression = (org.eclipse.jdt.internal.compiler.ast.Expression) this.newAstToOldAst
						.get(expression);
				compilerExpression.resolvedType = ((org.eclipse.jdt.core.dom.TypeBinding) typeBinding).binding;
				this.newAstToOldAst.put(expression, compilerExpression);
			} else if (typeBinding == null && expression instanceof ArrayAccess) {
				org.eclipse.jdt.internal.compiler.ast.Expression compilerExpression = (org.eclipse.jdt.internal.compiler.ast.Expression) this.newAstToOldAst
						.get(expression);
	
				if (compilerExpression instanceof ArrayReference) {
					ArrayReference aReference = (ArrayReference) compilerExpression;
					if (aReference.receiver instanceof NameReference) {
						Binding binding = ((NameReference) aReference.receiver).binding;
						if (binding instanceof VariableBinding) {
							TypeBinding tBinding = ((VariableBinding) binding).type;
							if (tBinding instanceof ArrayBinding) {
								String name = new String(
										((ArrayBinding) tBinding).leafComponentType
												.readableName());
								CompilationUnit cu = (CompilationUnit) PPAASTUtil
										.getSpecificParentType(expression,
												ASTNode.COMPILATION_UNIT);
								typeBinding = typeRegistry.getTypeBinding(cu, name,
										this, false, new PPATypeBindingOptions());
								this.bindingsToAstNodes
										.put(typeBinding, expression);
								String key = typeBinding.getKey();
								if (key != null) {
									this.bindingTables.bindingKeysToBindings.put(
											key, typeBinding);
								}
	
								// Fix for future use
								compilerExpression.resolvedType = ((org.eclipse.jdt.core.dom.TypeBinding) typeBinding).binding;
								this.newAstToOldAst.put(expression,
										compilerExpression);
							}
						}
					}
	
				}
	
			}
		}catch(Exception e){
			System.out.println("Error in synchronized ITypeBinding resolveExpressionType(Expression expression) {");
			exdist.ExceptionHandler.process(e, "Error in synchronized ITypeBinding resolveExpressionType(Expression expression) {");
		}
		return typeBinding;
	}

	@Override
	@SuppressWarnings("unchecked")
	synchronized ITypeBinding resolveType(AnonymousClassDeclaration type) {
		ITypeBinding tBinding = super.resolveType(type);

		if (tBinding == null) {
			String fqn = PPAASTUtil.getNameFromAnon(type);
			CompilationUnit cu = (CompilationUnit) PPAASTUtil
					.getSpecificParentType(type, ASTNode.COMPILATION_UNIT);
			tBinding = typeRegistry.getTypeBinding(cu, fqn, this, false,
					new PPATypeBindingOptions());
			this.bindingsToAstNodes.put(tBinding, type);
			String key = tBinding.getKey();
			if (key != null) {
				this.bindingTables.bindingKeysToBindings.put(key, tBinding);
			}
		}

		return tBinding;
	}

	public void setCurrentCu(CompilationUnit currentCu) {
		// XXX This is a hack and will need to be fixed!
		this.currentCu = currentCu;
	}



}
