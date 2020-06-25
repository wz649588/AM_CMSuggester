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
package ca.mcgill.cs.swevo.ppa;

import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;


public class TypeFactMerger {

	public TypeFact findTypeFact(TypeFact fact, List<TypeFact> facts) {
		TypeFact foundFact = null;

		for (TypeFact tempFact : facts) {
			if (tempFact.getIndex().equals(fact.getIndex())) {
				foundFact = tempFact;
				break;
			}
		}

		return foundFact;
	}

	public boolean isSafer(TypeFact typeFact1, TypeFact typeFact2) {
		return PPABindingsUtil.isSafer(typeFact1.getNewType(), typeFact2.getNewType());
	}

	public boolean areComparable(TypeFact typeFact1, TypeFact typeFact2) {
		ITypeBinding binding1 = typeFact1.getNewType();
		ITypeBinding binding2 = typeFact2.getNewType();
		
		return (PPABindingsUtil.isSuperMissingType(binding1) && PPABindingsUtil.isSuperMissingType(binding2))
				|| (PPABindingsUtil.isFullType(binding1) && PPABindingsUtil.isFullType(binding2));
	}
	
	public boolean isValuableTypeFact(TypeFact typeFact) {
		return PPABindingsUtil.isSafer(typeFact.getNewType(), typeFact.getOldType()) && !nullType(typeFact.getNewType());
	}

	private boolean nullType(ITypeBinding newType) {
		return newType.getName().equals("null");
	}

	public TypeFact merge(TypeFact oldTypeFact, TypeFact newTypeFact) {
		TypeFact mergedFact = null;

		if (isSafer(newTypeFact, oldTypeFact)) {
			mergedFact = newTypeFact;
			mergedFact.addConstraint(oldTypeFact);
		} else if (areComparable(newTypeFact, oldTypeFact)) {
			// TODO Try to refine the typefacts or find the most precise based on the direction.
			mergedFact = oldTypeFact;
		} else {
			mergedFact = oldTypeFact;
			mergedFact.addConstraint(newTypeFact);
		}

		return mergedFact;
	}

	public boolean similarTypeFacts(TypeFact typeFact, TypeFact currentFact) {
		return currentFact != null && typeFact.getIndex().equals(currentFact.getIndex()) && typeFact.getNewType().isEqualTo(currentFact.getNewType()) && typeFact.getNewDirection() == currentFact.getNewDirection();
	}

}
