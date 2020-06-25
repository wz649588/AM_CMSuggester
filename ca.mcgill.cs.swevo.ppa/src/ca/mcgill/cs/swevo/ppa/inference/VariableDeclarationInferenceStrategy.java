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
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class VariableDeclarationInferenceStrategy extends AbstractInferenceStrategy {

	public VariableDeclarationInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
		VariableDeclarationFragment fragment = (VariableDeclarationFragment) node;
		ITypeBinding newBinding = fragment.getName().resolveTypeBinding();
		Expression exp = fragment.getInitializer();
		if (!indexer.isSafe(exp)) {
			TypeFact tFact = new TypeFact(indexer.getMainIndex(exp), exp.resolveTypeBinding(),
					TypeFact.UNKNOWN, newBinding, TypeFact.SUBTYPE, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		}
	}

	public boolean isSafe(ASTNode node) {
		VariableDeclarationFragment fragment = (VariableDeclarationFragment) node;
		Expression exp = fragment.getInitializer();

		return indexer.isSafe(exp);
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		// Do nothing.
	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		// Do nothing.
	}

}
