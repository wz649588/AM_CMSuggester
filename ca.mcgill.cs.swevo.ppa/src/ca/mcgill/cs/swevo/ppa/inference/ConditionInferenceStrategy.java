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

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.WhileStatement;

import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class ConditionInferenceStrategy extends AbstractInferenceStrategy {

	public ConditionInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
		Expression exp = getExpression(node);

		if (!indexer.isSafe(exp)) {
			ITypeBinding newBinding = ppaEngine.getRegistry().getPrimitiveBinding("boolean", exp);
			ITypeBinding oldBinding = exp.resolveTypeBinding();
			TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.CONDITION_STRATEGY);
			ppaEngine.reportTypeFact(typeFact);
		}
	}

	public boolean isSafe(ASTNode node) {
		Expression exp = getExpression(node);

		return exp == null || !indexer.isIndexable(exp) || indexer.isSafe(exp);
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {

	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {

	}

	private Expression getExpression(ASTNode node) {
		Expression exp = null;

		if (node instanceof ForStatement) {
			ForStatement forStatement = (ForStatement) node;
			exp = forStatement.getExpression();
		} else if (node instanceof IfStatement) {
			IfStatement ifStatement = (IfStatement) node;
			exp = ifStatement.getExpression();
		} else if (node instanceof WhileStatement) {
			WhileStatement whileStatement = (WhileStatement) node;
			exp = whileStatement.getExpression();
		} else if (node instanceof DoStatement) {
			DoStatement doStatement = (DoStatement) node;
			exp = doStatement.getExpression();
		}

		return exp;
	}

}
