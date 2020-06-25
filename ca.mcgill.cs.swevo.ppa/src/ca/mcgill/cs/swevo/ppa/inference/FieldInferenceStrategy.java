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
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.QualifiedName;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;
import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class FieldInferenceStrategy extends AbstractInferenceStrategy {

	public FieldInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
	}

	public void inferTypes(ASTNode node) {
	}

	public boolean hasDeclaration(ASTNode node) {
		return !ppaEngine.getAmbiguousNodes().contains(node);
	}
	
	public boolean isSafe(ASTNode node) {
		boolean isSafe = hasDeclaration(node);

		if (!isSafe) {
			SimpleName sName = (SimpleName) node;
//			ASTNode pNode = node.getParent();
//			if (pNode instanceof QualifiedName) {
//				QualifiedName qNode = (QualifiedName)pNode;
//				Name n = qNode.getQualifier();
//				ITypeBinding itb = n.resolveTypeBinding();
//				
//			}
			IVariableBinding varBinding = (IVariableBinding) sName.resolveBinding();
//			if (varBinding.isField()) {
//				ITypeBinding tb = varBinding.getDeclaringClass();
//				IVariableBinding[] vbs = tb.getDeclaredFields();
//				for (int i = 0; i < vbs.length; i++) {
//					if (vbs[i].equals(varBinding)) {
//						System.out.println("found");
//					} else
//						System.out.println(vbs[i].getKey());
//				}
//				ITypeBinding tb2 = tb.getSuperclass();
//				vbs = tb2.getDeclaredFields();
//				for (int i = 0; i < vbs.length; i++) {
//					if (vbs[i].equals(varBinding)) {
//						System.out.println("found");
//					} else 
//						System.out.println(vbs[i].getKey());
//				}
//				System.out.print(tb);
//			}
			ITypeBinding container = varBinding.getDeclaringClass();
			ITypeBinding fb = varBinding.getType();
			isSafe = container == null || (!PPABindingsUtil.isMissingType(container) && !PPABindingsUtil.isUnknownType(container)
					&& !PPABindingsUtil.isMissingType(fb) && !PPABindingsUtil.isUnknownType(fb));//added by nameng
		}
		
		return isSafe;
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		SimpleName sName = (SimpleName) node;
		PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
		PPADefaultBindingResolver resolver = getResolver(sName);

		// The field's type changed.
		if (typeFact.getIndex().equals(getMainIndex(node))) {
			IVariableBinding varBinding = (IVariableBinding) sName.resolveBinding();
			ITypeBinding newType = typeFact.getNewType();
			IVariableBinding newBinding = typeRegistry.getFieldBindingWithType(
					varBinding.getName(), varBinding.getDeclaringClass(), newType, resolver);

			resolver.fixFieldBinding(sName, newBinding);
		}
		// The field's container changed.
//		else {
//			
//			//
//
//		}
	}
	

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		SimpleName sName = (SimpleName) node;
		PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
		PPADefaultBindingResolver resolver = getResolver(sName);
		ASTNode newContainerNode = PPAASTUtil.getFieldContainer(node, true, false);
		ITypeBinding newContainer = PPABindingsUtil.getTypeBinding(newContainerNode);

		if (newContainer == null) {
			return;
		}
		
		IVariableBinding varBinding = (IVariableBinding) sName.resolveBinding();
		IVariableBinding newFieldBinding = null;

		if (PPABindingsUtil.isMissingType(newContainer)) {
			newFieldBinding = typeRegistry.getFieldBinding(varBinding.getName(), newContainer,
					varBinding.getType(), resolver);
		} else {
			// Maybe we can find the field declaration
			newFieldBinding = PPABindingsUtil.findFieldHierarchy(newContainer, sName.getFullyQualifiedName());
			if (newFieldBinding == null) {
				// We did not find the field in the container, try to find a suitable container (missing type)
				ITypeBinding tempContainer = PPABindingsUtil.getFirstMissingSuperType(newContainer);
				if (tempContainer != null) {
					newContainer = tempContainer;
					newFieldBinding = typeRegistry.getFieldBinding(varBinding.getName(), newContainer,
							varBinding.getType(), resolver);
				} else {
					newFieldBinding = typeRegistry.getFieldBinding(varBinding.getName(), newContainer,
							varBinding.getType(), resolver);
				}
			} else {
				// In case we found the field in a super type of the container.
				newContainer = newFieldBinding.getDeclaringClass();
			}
		}

		// Check field type
		ITypeBinding newFieldType = newFieldBinding.getType();
		ITypeBinding oldFieldType = varBinding.getType();
		if (!newFieldType.isEqualTo(oldFieldType)) {
			if (PPABindingsUtil.isSafer(newFieldType, oldFieldType)) {
				resolver.fixFieldBinding(sName, newFieldBinding);
				TypeFact tFact = new TypeFact(indexer.getMainIndex(sName), oldFieldType,
						TypeFact.UNKNOWN, newFieldType, TypeFact.EQUALS,
						TypeFact.FIELD_STRATEGY);
				ppaEngine.reportTypeFact(tFact);
				
			} else if (!PPABindingsUtil.isMissingType(newContainer)) {
				resolver.fixFieldBinding(sName, newFieldBinding);
				// This is the case where we found the field declaration and the field is "less" safe than the previous type.
				// XXX The oldType = Unknown is to ensure that the new type will be pushed.
				TypeFact tFact = new TypeFact(indexer.getMainIndex(sName), typeRegistry
						.getUnknownBinding(resolver), TypeFact.UNKNOWN, newFieldType,
						TypeFact.EQUALS, TypeFact.FIELD_STRATEGY);
				ppaEngine.reportTypeFact(tFact);
			} else {
				// This is an odd case: we found a ppa generated field, but the type we got before was safer.
				newFieldBinding = typeRegistry.getFieldBindingWithType(varBinding.getName(),
						newContainer, varBinding.getType(), resolver);
				resolver.fixFieldBinding(sName, newFieldBinding);
			}
		} else {
			resolver.fixFieldBinding(sName, newFieldBinding);
		}
		
	}

	@Override
	public PPAIndex getMainIndex(ASTNode node) {
		SimpleName sName = (SimpleName) node;
		IVariableBinding vBinding = (IVariableBinding) sName.resolveBinding();

		return new PPAIndex(vBinding);
	}

	@Override
	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		List<PPAIndex> indexes = super.getSecondaryIndexes(node);
		ASTNode fieldContainer = PPAASTUtil.getFieldContainer(node, true, false);

		if (indexer.isIndexable(fieldContainer)) {
			PPAIndex tempIndex = indexer.getMainIndex(fieldContainer);
			indexes.add(tempIndex);
		}

		return indexes;
	}

}
