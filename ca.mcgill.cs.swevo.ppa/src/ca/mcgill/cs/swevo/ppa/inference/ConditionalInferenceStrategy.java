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
package ca.mcgill.cs.swevo.ppa.inference;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class ConditionalInferenceStrategy extends AbstractInferenceStrategy {

	public ConditionalInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
		ConditionalExpression conditional = (ConditionalExpression) node;
		
		inferCondition(conditional.getExpression());
		ITypeBinding binding = inferThenElse(conditional.getThenExpression(), conditional.getElseExpression());
		inferConditional(conditional, binding, true);
	}
	
	private void inferConditional(ConditionalExpression conditional,
			ITypeBinding newBinding, boolean forceFixInternal) {
		ITypeBinding currentBinding = conditional.resolveTypeBinding();
		
		boolean unsafe = currentBinding == null || PPABindingsUtil.isUnknownType(currentBinding);
		
		if (unsafe && !PPABindingsUtil.isUnknownType(newBinding)) {
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(conditional), currentBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
			ppaEngine.getRegistry().fixConditional(conditional, newBinding);
		} else if (forceFixInternal) {
			// Necessary if it is unknown for the first pass.
			if (currentBinding != null) {
				ppaEngine.getRegistry().fixConditional(conditional, currentBinding);
			} else {
				PPADefaultBindingResolver resolver = getResolver(conditional);
				ITypeBinding unknown = ppaEngine.getRegistry().getUnknownBinding(resolver);
				ppaEngine.getRegistry().fixConditional(conditional, unknown);
			}
		}
		
		
	}

	private ITypeBinding inferThenElse(Expression thenExpression,
			Expression elseExpression) {
		boolean thenSafe = indexer.isSafe(thenExpression);
		boolean elseSafe = indexer.isSafe(elseExpression);
		PPADefaultBindingResolver resolver = getResolver(thenExpression);
		ITypeBinding finalBinding = ppaEngine.getRegistry().getUnknownBinding(resolver);
		if (thenSafe && !elseSafe) {
			ITypeBinding newBinding = thenExpression.resolveTypeBinding();
			ITypeBinding oldBinding = elseExpression.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(elseExpression), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
			finalBinding = newBinding;
		} else if (!thenSafe && elseSafe) {
			ITypeBinding newBinding = elseExpression.resolveTypeBinding();
			ITypeBinding oldBinding = thenExpression.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(thenExpression), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
			finalBinding = newBinding;
		} else if (thenSafe && elseSafe) {
			finalBinding = thenExpression.resolveTypeBinding();
		}
		return finalBinding;
	}
	
	private void pushThenElse(Expression thenExpression, Expression elseExpression, ITypeBinding newBinding) {
		boolean thenSafe = indexer.isSafe(thenExpression);
		boolean elseSafe = indexer.isSafe(elseExpression);
		if (!elseSafe) {
			ITypeBinding oldBinding = elseExpression.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(elseExpression), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
		} 
		
		if (!thenSafe) {
			ITypeBinding oldBinding = thenExpression.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(thenExpression), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
		}
	}

	private void inferCondition(Expression exp) {
		if (!indexer.isSafe(exp)) {
			ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("boolean", exp);
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
		}
	}

	public boolean isSafe(ASTNode node) {
		ConditionalExpression conditional = (ConditionalExpression) node;
		ITypeBinding typeBinding = conditional.resolveTypeBinding();
		boolean isSafe = typeBinding != null && !PPABindingsUtil.isUnknownType(typeBinding) &&
				indexer.isSafe(conditional.getExpression()) && 
				indexer.isSafe(conditional.getThenExpression()) && indexer.isSafe(conditional.getElseExpression());
		return isSafe;
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		ConditionalExpression conditional = (ConditionalExpression) node;
		pushThenElse(conditional.getThenExpression(), conditional.getElseExpression(), typeFact.getNewType());
		inferConditional(conditional, typeFact.getNewType(), false);
	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		ConditionalExpression conditional = (ConditionalExpression) node;
		
		inferCondition(conditional.getExpression());
		ITypeBinding binding = inferThenElse(conditional.getThenExpression(), conditional.getElseExpression());
		inferConditional(conditional, binding, false);
	}
	
	@Override
	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		List<PPAIndex> list = super.getSecondaryIndexes(node);
		ConditionalExpression conditional = (ConditionalExpression) node;
		Expression condition = conditional.getExpression();
		Expression left = conditional.getThenExpression();
		Expression right = conditional.getElseExpression();
		if (indexer.isIndexable(condition)) {
			list.add(indexer.getMainIndex(condition));
		}
		
		if (indexer.isIndexable(left)) {
			list.add(indexer.getMainIndex(left));
		}

		if (indexer.isIndexable(right)) {
			list.add(indexer.getMainIndex(right));
		}

		return list;
	}

}
