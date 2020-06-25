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

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public interface TypeInferenceStrategy {

	public boolean hasDeclaration(ASTNode node);
	
	public boolean isSafe(ASTNode node);
	
	public void inferTypes(ASTNode node);
	
	public void makeSafe(ASTNode node, TypeFact typeFact);
	
	public PPAIndex getMainIndex(ASTNode node);
	
	public List<PPAIndex> getSecondaryIndexes(ASTNode node);

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact);
	
}
