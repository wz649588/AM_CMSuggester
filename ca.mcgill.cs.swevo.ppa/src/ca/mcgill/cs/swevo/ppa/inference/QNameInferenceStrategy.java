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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class QNameInferenceStrategy extends AbstractInferenceStrategy {

	public QNameInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
	}

	public boolean isSafe(ASTNode node) {
		QualifiedName qName = (QualifiedName) node;
		boolean leftSafe = true;
		boolean rightSafe = true;

		Expression left = qName.getQualifier();
		Expression right = qName.getName();

		if (indexer.isIndexable(left)) {
			leftSafe = indexer.isSafe(left);
		}

		if (indexer.isIndexable(right)) {
			rightSafe = indexer.isSafe(right);
		}

		return leftSafe && rightSafe;
	}

	private boolean qNameChanged(ASTNode node, TypeFact typeFact) {
		return typeFact.getIndex().equals(getMainIndex(node));
	}

	// private boolean nameChanged(ASTNode node, TypeFact typeFact) {
	// boolean nameChanged = false;
	//
	// QualifiedName qName = (QualifiedName) node;
	// Expression right = qName.getName();
	//
	// if (indexer.isIndexable(right)) {
	// nameChanged = typeFact.getIndex().equals(indexer.getMainIndex(right));
	// }
	//
	// return nameChanged;
	// }

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		QualifiedName qName = (QualifiedName) node;
		Name right = qName.getName();

		if (qNameChanged(node, typeFact)) {
			if (!indexer.isSafe(right)) {
				ITypeBinding oldBinding = typeFact.getOldType();
				ITypeBinding newBinding = typeFact.getNewType();
				ITypeBinding rightBinding = getRightBinding(right);
				if (rightBinding == null || !rightBinding.isEqualTo(newBinding)) {
					TypeFact tFact = new TypeFact(indexer.getMainIndex(right), oldBinding, typeFact
							.getOldDirection(), newBinding, typeFact.getNewDirection(), typeFact
							.getStrategy());
					ppaEngine.reportTypeFact(tFact);
				}
			}
			// } else if (nameChanged(node, typeFact)) {
		}
		// else {
		//			
		// }
	}

	/**
	 * This method is necessary because resolveTypeBinding for a qualified name may result in
	 * checking the declared class of a field instead of looking at the type of the previous field.
	 * 
	 * @param right
	 * @return
	 */
	private ITypeBinding getRightBinding(Name right) {
		IBinding binding = null;
		try {//the try-catch is added by nameng to handle exception thrown out by jdt
			binding = right.resolveBinding();
		} catch (Exception e) {
			//do nothing
		}
		ITypeBinding typeBinding = null;
		if (binding != null && binding instanceof IVariableBinding) {
			IVariableBinding varBinding = (IVariableBinding) binding;
			typeBinding = varBinding.getType();
		} else {
			typeBinding = right.resolveTypeBinding();
		}

		return typeBinding;
	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		ITypeBinding oldBinding = typeFact.getOldType();
		QualifiedName qName = (QualifiedName) node;
		Expression left = qName.getQualifier();
		Expression right = qName.getName();

		if (indexer.isIndexable(right) && indexer.getMainIndex(right).equals(typeFact.getIndex())) {
			ITypeBinding newBinding = PPABindingsUtil.getTypeBinding(right);

			// ITypeBinding realBinding = qName.resolveTypeBinding();
			TypeFact tFact = new TypeFact(getMainIndex(node), oldBinding, typeFact
					.getOldDirection(), newBinding, typeFact.getNewDirection(), typeFact
					.getStrategy());
			ppaEngine.reportTypeFact(tFact);
		}

		if (indexer.isIndexable(left) && indexer.getMainIndex(left).equals(typeFact.getIndex())) {

		}

	}

	@Override
	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		QualifiedName qName = (QualifiedName) node;
		List<PPAIndex> indexes = new ArrayList<PPAIndex>();

		Expression left = qName.getQualifier();
		Expression right = qName.getName();

		if (indexer.isIndexable(left)) {
			PPAIndex tempIndex = indexer.getMainIndex(left);
			indexes.add(tempIndex);
		}

		if (indexer.isIndexable(right)) {
			PPAIndex tempIndex = indexer.getMainIndex(right);
			indexes.add(tempIndex);
		}

		return indexes;
	}

}
