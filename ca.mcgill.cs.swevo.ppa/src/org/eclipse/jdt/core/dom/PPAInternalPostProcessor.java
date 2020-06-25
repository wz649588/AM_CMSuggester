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

import java.util.Hashtable;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.ExplicitConstructorCall;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.OperatorExpression;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.eclipse.jdt.internal.compiler.ast.ThrowStatement;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemMethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

/**
 * <p>
 * This visitor is responsible for copying inferred type binding into ast node
 * properties that are specific to certain type of AST node. For example, the
 * ThrowStatement has a exceptionType field that is a copy of the type binding
 * of the exception field.
 * </p>
 * 
 * @author Barthelemy Dagenais
 * 
 */
public class PPAInternalPostProcessor extends ASTVisitor {

	// private InternalASTNodeFixer fixer = new InternalASTNodeFixer();

	private PPADefaultBindingResolver resolver;

	private PPATypeRegistry registry;

//	private Hashtable<String, ITypeBinding> typeTable;

	public PPAInternalPostProcessor(PPADefaultBindingResolver resolver,
			PPATypeRegistry registry) {
		this.resolver = resolver;
		this.registry = registry;
//		this.typeTable = typeTable;
	}
	

//	@Override
//	public boolean visit(QualifiedNameReference qualifiedNameReference,
//			ClassScope scope) {
//		// TODO Auto-generated method stub
//		TypeBinding quaB = qualifiedNameReference.resolveType(scope);
//		boolean bUnknown = PPABindingsUtil.isUnknownType(quaB);
//		return super.visit(qualifiedNameReference, scope);
//	}

	@Override
	public void endVisit(ExplicitConstructorCall explicitConstructor,
			BlockScope scope) {
		// FIX super(...) binding
		MethodBinding mBinding = explicitConstructor.binding;
		boolean isSuper = explicitConstructor.isImplicitSuper()
				|| explicitConstructor.isSuper()
				|| explicitConstructor.isSuperAccess();
		boolean isProblematic = mBinding == null
				|| mBinding instanceof ProblemMethodBinding;
		if (isSuper && isProblematic) {
			fixSuperInvocation(explicitConstructor, scope);
		}
	}

	/**
	 * <p>
	 * This is the place to fix the super(...) because super(...) never
	 * influences type inference, but it can benefit from it. Waiting at the end
	 * thus makes sense.
	 * </p>
	 * 
	 * @param explicitConstructor
	 * @param scope
	 */
	@SuppressWarnings("unchecked")
	private void fixSuperInvocation(
			ExplicitConstructorCall explicitConstructor, BlockScope scope) {
		int size = 0;
		
		if (explicitConstructor.arguments == null) {
			size = 0;
		} else {
			size = explicitConstructor.arguments.length;
		}
		
		ITypeBinding[] arguments = new ITypeBinding[size];
		for (int i = 0; i < size; i++) {
			arguments[i] = new org.eclipse.jdt.core.dom.TypeBinding(
					this.resolver,
					explicitConstructor.arguments[i].resolvedType);
		}

		TypeReference superReference = scope.classScope().referenceContext.superclass;
		if (superReference != null) {
			TypeBinding superBinding = superReference.resolvedType;
			if (superBinding == null) {
				superBinding = registry.getInternalUnknownBinding(resolver);
			}
			try{
				if(superBinding instanceof ArrayBinding){
					ArrayBinding ab = (ArrayBinding)superBinding;
					superBinding = ab.leafComponentType();
				}
				MethodBinding newBinding = registry.getInternalConstructorBinding(
						(ReferenceBinding) superBinding, size, arguments, resolver);
				explicitConstructor.binding = newBinding;
				resolver.bindingTables.compilerBindingsToASTBindings.put(
						newBinding, new org.eclipse.jdt.core.dom.MethodBinding(
								resolver, newBinding));
			}catch(ClassCastException e){
				System.out.println("private void fixSuperInvocation is Passed. zhh ");
				exdist.ExceptionHandler.process(e, "private void fixSuperInvocation is Passed. zhh ");
			}
		}
	}

	@Override
	public void endVisit(ThrowStatement throwStatement, BlockScope scope) {
		if (throwStatement.exceptionType == null) {
			throwStatement.exceptionType = throwStatement.exception.resolvedType;
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public void endVisit(MessageSend messageSend, BlockScope scope) {
		MethodBinding mBinding = messageSend.binding;
		
		org.eclipse.jdt.internal.compiler.ast.Expression receiver = messageSend.receiver;
		if (receiver != null) {
			Object receiverBinding = getBinding(receiver);
			// If the receiver is a Type, it means the method is static. The
			// flag is not set when a method is inferred by PPA.
			if(!(receiverBinding instanceof BinaryTypeBinding)){
				if (receiverBinding instanceof org.eclipse.jdt.internal.compiler.lookup.TypeBinding
						&& !(receiver instanceof ThisReference)) {
					if(mBinding!=null){
						mBinding.modifiers |= ClassFileConstants.AccStatic;
						resolver.bindingTables.compilerBindingsToASTBindings.put(
								mBinding, new org.eclipse.jdt.core.dom.MethodBinding(
										resolver, mBinding));
					}
				}
			}
		}
	}

	@Override
	public void endVisit(BinaryExpression binaryExpression, BlockScope scope) {
		if (binaryExpression.resolvedType == null) {
			Binding binding = getBinding(binaryExpression.left);
			if (binding instanceof TypeBinding) {
				binaryExpression.resolvedType = (TypeBinding) binding;
			} else if (binding instanceof org.eclipse.jdt.internal.compiler.lookup.VariableBinding) {
				org.eclipse.jdt.internal.compiler.lookup.VariableBinding vBinding = (org.eclipse.jdt.internal.compiler.lookup.VariableBinding) binding;
				binaryExpression.resolvedType = vBinding.type;
			} else if (binding instanceof MethodBinding) {
				MethodBinding mBinding = (MethodBinding) binding;
				binaryExpression.resolvedType = mBinding.returnType;
			}
		}

		
		boolean success = false;
		if(binaryExpression.left.resolvedType!=null&&binaryExpression.right.resolvedType!=null){
			success = setBinaryBits(binaryExpression,
					binaryExpression.left.resolvedType.id,
					binaryExpression.right.resolvedType.id);
		}//zhh				
		if (!success) {
			if(binaryExpression.resolvedType!=null&&binaryExpression.resolvedType!=null){
				success = setBinaryBits(binaryExpression,
						binaryExpression.resolvedType.id,
						binaryExpression.resolvedType.id);
			}//zhh
		}
		if (!success) {
			setBinaryBits(binaryExpression,
					OperatorExpression.T_JavaLangString,
					OperatorExpression.T_JavaLangString);
		}
	}

	private boolean setBinaryBits(BinaryExpression binaryExpression,
			int leftTypeID, int rightTypeID) {
		boolean success = true;

		try {
			int operator = (binaryExpression.bits & org.eclipse.jdt.internal.compiler.ast.ASTNode.OperatorMASK) >> org.eclipse.jdt.internal.compiler.ast.ASTNode.OperatorSHIFT;
			int operatorSignature = OperatorExpression.OperatorSignatures[operator][(leftTypeID << 4)
					+ rightTypeID];
			binaryExpression.bits |= operatorSignature & 0xF;
		} catch (ArrayIndexOutOfBoundsException e) {
			success = false;
		}

		return success;
	}

	public Binding getBinding(Expression expression) {
		Binding binding = org.eclipse.jdt.internal.compiler.ast.Expression
				.getDirectBinding(expression);
		if (binding == null) {
			binding = expression.resolvedType;
		}
		return binding;
	}

	// @Override
	// public void endVisit(TryStatement tryStatement, BlockScope scope) {
	// fixer.fixCatchBlock(tryStatement);
	// }

}
