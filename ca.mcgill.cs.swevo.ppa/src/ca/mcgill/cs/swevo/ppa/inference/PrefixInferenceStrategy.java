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
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PrefixExpression;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class PrefixInferenceStrategy extends AbstractInferenceStrategy {

	public PrefixInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
		processOperators((PrefixExpression) node, null);
	}

	public boolean isSafe(ASTNode node) {
		PrefixExpression prefix = (PrefixExpression) node;
		Expression exp = prefix.getOperand();
		ITypeBinding tb = prefix.resolveTypeBinding();
		return (!indexer.isIndexable(exp) || indexer.isSafe(exp)) && (tb != null);//added by nameng tb!= null, because even though exp is resolvable, the prefix may be still unresolvable
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		processOperators((PrefixExpression) node, typeFact);
	}

	public void makeSafeSecondary(ASTNode node, TypeFact newFact) {
//		processOperators((PrefixExpression) node, typeFact);//commented by nameng
		PrefixExpression node2 = (PrefixExpression)node;
		ITypeBinding newType = null;
		Expression exp = node2.getOperand();
		boolean isPrimary = newFact != null
				&& indexer.getMainIndex(node2).equals(newFact.getIndex());
		boolean isSafe = indexer.isSafe(exp) || (newFact != null && !isPrimary);
		if (node2.getOperator() != PrefixExpression.Operator.NOT) {
			if (isPrimary && !isSafe) {
				ITypeBinding newBinding = newFact.getNewType();
				ITypeBinding oldBinding = exp.resolveTypeBinding();
				TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
						TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
				ppaEngine.reportTypeFact(typeFact);
				newType = newBinding;
			} else if (!isSafe) {
				ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("int", exp);
				ITypeBinding oldBinding = exp.resolveTypeBinding();
				TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
						TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
				ppaEngine.reportTypeFact(typeFact);
				newType = newBinding;
			}
		} else if (!isSafe) {
			ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("boolean", exp);
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
			newType = newBinding;
		} else {//added by nameng isSafe and node2.getOperator() == NOT
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			if (oldBinding != null)
				newType = oldBinding;
			else 
				newType = ppaEngine.getRegistry().getPrimitiveBinding("boolean", node2);
			ppaEngine.getRegistry().fixUnary(node2, newType);
		}

		if (newType != null && !isPrimary) {
			ITypeBinding oldBinding = node2.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(node2), oldBinding,
					TypeFact.UNKNOWN, newType, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);//modified by nameng from BINARY_STRATEGY to UNARY_STRATEGY
			ppaEngine.reportTypeFact(typeFact);
			// report new type for this expression.
			// fix this expression.
		} else if (isPrimary) {
			if (newType != null) {
				ppaEngine.getRegistry().fixUnary(node2, newType);
			} else if (newFact != null) {
				ppaEngine.getRegistry().fixUnary(node2, newFact.getNewType());
			}
		}
	}

	private void processOperators(PrefixExpression node, TypeFact newFact) {
		ITypeBinding newType = null;
		Expression exp = node.getOperand();
		boolean isPrimary = newFact != null
				&& indexer.getMainIndex(node).equals(newFact.getIndex());
		boolean isSafe = indexer.isSafe(exp) || (newFact != null && !isPrimary);
		if (node.getOperator() != PrefixExpression.Operator.NOT) {
			if (isPrimary && !isSafe) {
				ITypeBinding newBinding = newFact.getNewType();
				ITypeBinding oldBinding = exp.resolveTypeBinding();
				TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
						TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
				ppaEngine.reportTypeFact(typeFact);
				newType = newBinding;
			} else if (!isSafe) {
				ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("int", exp);
				ITypeBinding oldBinding = exp.resolveTypeBinding();
				TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
						TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
				ppaEngine.reportTypeFact(typeFact);
				newType = newBinding;
			}
		} else if (!isSafe) {
			ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("boolean", exp);
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
			newType = newBinding;
		} else {//added by nameng isSafe and node2.getOperator() == NOT
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			if (oldBinding != null)
				newType = oldBinding;
			else 
				newType = ppaEngine.getRegistry().getPrimitiveBinding("boolean", node);
			ppaEngine.getRegistry().fixUnary(node, newType);
		}

		if (newType != null && !isPrimary) {
			ITypeBinding oldBinding = node.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(node), oldBinding,
					TypeFact.UNKNOWN, newType, TypeFact.SUBTYPE, TypeFact.UNARY_STRATEGY);//modified by nameng from BINARY_STRATEGY to UNARY_STRATEGY
			ppaEngine.reportTypeFact(typeFact);
			// report new type for this expression.
			// fix this expression.
		} else if (isPrimary) {
			if (newType != null) {
				ppaEngine.getRegistry().fixUnary(node, newType);
			} else if (newFact != null) {
				ppaEngine.getRegistry().fixUnary(node, newFact.getNewType());
			}
		}
	}

	@Override
	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		List<PPAIndex> list = super.getSecondaryIndexes(node);
		PrefixExpression prefix = (PrefixExpression) node;
		Expression exp = prefix.getOperand();
		if (indexer.isIndexable(exp)) {
			list.add(indexer.getMainIndex(exp));
		}
		return list;
	}

}
