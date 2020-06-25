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
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.ReturnStatement;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;


public class ReturnInferenceStrategy extends AbstractInferenceStrategy {

	public ReturnInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
		ReturnStatement returnStmt = (ReturnStatement) node;

		Expression exp = returnStmt.getExpression();

		if (exp == null || !indexer.isIndexable(exp) || indexer.isSafe(exp)) {
			return;
		}

		MethodDeclaration mDeclaration = (MethodDeclaration) PPAASTUtil.getSpecificParentType(
				returnStmt, ASTNode.METHOD_DECLARATION);
		if (mDeclaration != null) {
			IMethodBinding methodBinding = mDeclaration.resolveBinding();
			if (methodBinding != null) {
				ITypeBinding newBinding = methodBinding.getReturnType();
				ITypeBinding oldBinding = exp.resolveTypeBinding();
				TypeFact typeFact = new TypeFact(indexer.getMainIndex(exp), oldBinding,
						TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.RETURN_STRATEGY);
				ppaEngine.reportTypeFact(typeFact);
			}
		}
	}

	public boolean isSafe(ASTNode node) {
		ReturnStatement returnStmt = (ReturnStatement) node;

		Expression exp = returnStmt.getExpression();

		return exp == null || !indexer.isIndexable(exp) || indexer.isSafe(exp);
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
	}
	
}
