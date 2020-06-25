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
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class AssignInferenceStrategy extends AbstractInferenceStrategy {
	public AssignInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	private boolean isLeftSafe(ASTNode node) {
		boolean leftSafe = true;
		Assignment assign = (Assignment) node;
		Expression left = assign.getLeftHandSide();
		if (indexer.isIndexable(left)) {
			leftSafe = indexer.isSafe(left);
		}
		return leftSafe;
	}

	private boolean isRightSafe(ASTNode node) {
		boolean rightSafe = true;
		Assignment assign = (Assignment) node;
		Expression right = assign.getRightHandSide();
		if (indexer.isIndexable(right)) {
			rightSafe = indexer.isSafe(right);
		}
		return rightSafe;
	}

	public void inferTypes(ASTNode node) {
		Assignment assign = (Assignment) node;
		Expression left = assign.getLeftHandSide();
		Expression right = assign.getRightHandSide();
		ITypeBinding leftBinding = PPABindingsUtil.getTypeBinding(left);
		ITypeBinding rightBinding = PPABindingsUtil.getTypeBinding(right);
		ITypeBinding assignBinding = assign.resolveTypeBinding();
		boolean isLeftSafe = isLeftSafe(node);
		boolean isRightSafe = isRightSafe(node);
		boolean isSafe = !(assignBinding == null||PPABindingsUtil.isProblemType(assignBinding));
		
		int leftValue = PPABindingsUtil.getSafetyValue(leftBinding);
		int rightValue = PPABindingsUtil.getSafetyValue(rightBinding);
		int value = PPABindingsUtil.getSafetyValue(assignBinding);

		if ((isLeftSafe && isRightSafe && isSafe) || (leftValue == rightValue&&leftValue == value)) {
			return;
		} else if (!isRightSafe && leftValue > rightValue) {
			TypeFact tFact = new TypeFact(indexer.getMainIndex(right), rightBinding,
					TypeFact.UNKNOWN, leftBinding, TypeFact.SUBTYPE, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		} else if (!isLeftSafe && rightValue > leftValue) {
			TypeFact tFact = new TypeFact(indexer.getMainIndex(left), leftBinding,
					TypeFact.UNKNOWN, rightBinding, TypeFact.SUPERTYPE, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		}
		if(!isSafe&&value<leftValue){//modified by nameng, because both left and right binding can be nonnull
			TypeFact tFact = new TypeFact(indexer.getMainIndex(node), assignBinding,
					TypeFact.UNKNOWN, leftBinding, TypeFact.SUPERTYPE, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		}else if(!isSafe&&value<rightValue){//modified by nameng, because both left and right binding can be nonnull
			TypeFact tFact = new TypeFact(indexer.getMainIndex(node), assignBinding,
					TypeFact.UNKNOWN, rightBinding, TypeFact.SUPERTYPE, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		}
	}

	public boolean isSafe(ASTNode node) {
		Assignment assign = (Assignment) node;
		boolean leftSafe = true;
		boolean rightSafe = true;
		boolean isSafe = true;
		
		ITypeBinding type = assign.resolveTypeBinding();
		isSafe = !(type == null||PPABindingsUtil.isProblemType(type));
		Expression left = assign.getLeftHandSide();
		Expression right = assign.getRightHandSide();

		leftSafe = indexer.isSafe(left);

		rightSafe = indexer.isSafe(right);

		return leftSafe && rightSafe && isSafe;
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		Assignment assign = (Assignment) node;
		ITypeBinding oldType = assign.resolveTypeBinding();
		ITypeBinding newType = typeFact.getNewType();
		if(PPABindingsUtil.getSafetyValue(oldType)<PPABindingsUtil.getSafetyValue(newType)){
			PPADefaultBindingResolver resolver = getResolver(assign);
			resolver.fixTypeBinding(assign, newType);
		}		
		inferTypes(node);
	}
	
	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		Assignment assign = (Assignment) node;
		ITypeBinding oldType = assign.resolveTypeBinding();
		ITypeBinding newType = typeFact.getNewType();
		if(PPABindingsUtil.getSafetyValue(oldType)<PPABindingsUtil.getSafetyValue(newType)){
			PPADefaultBindingResolver resolver = getResolver(assign);
			resolver.fixTypeBinding(assign, newType);
		}
		inferTypes(node);
	}

	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		Assignment assign = (Assignment) node;
		List<PPAIndex> indexes = new ArrayList<PPAIndex>();

		Expression left = assign.getLeftHandSide();
		Expression right = assign.getRightHandSide();

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
