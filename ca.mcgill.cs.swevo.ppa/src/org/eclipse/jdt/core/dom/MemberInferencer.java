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
package org.eclipse.jdt.core.dom;

import java.util.Hashtable;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.internal.compiler.lookup.PPATypeBindingOptions;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;

public class MemberInferencer {

	private PPAEngine engine;
	private PPAIndexer indexer;
	private PPATypeRegistry typeRegistry;
	private PPADefaultBindingResolver resolver;
	private Set<ASTNode> ambNodes;
	private Hashtable<String, ITypeBinding> typeTable;

	public MemberInferencer(PPAIndexer indexer,
			PPADefaultBindingResolver resolver, PPAEngine engine, Hashtable<String, ITypeBinding> typeTable) {
		this.indexer = indexer;
		this.engine = engine;
		this.typeRegistry = engine.getRegistry();
		this.resolver = resolver;
		this.ambNodes = engine.getAmbiguousNodes();
		this.typeTable = typeTable;
	}

	public void processMembers() {
		processFields();
		processMethods();
		processConstructors();
	}

	private void processMethods() {
		for (ASTNode node : ambNodes) {
			if (node instanceof SimpleName) {		
				SimpleName sName = (SimpleName) node;
				IBinding binding = null;
				try{
					binding = sName.resolveBinding();
				}catch(Exception e){
				}finally{
					if (isUnknownMethod(binding)) {
						PPABindingsUtil.fixMethod(sName, typeRegistry, resolver,
								indexer, engine);
					}
				}
			}
		}
	}

	private void processConstructors() {
		for (ASTNode node : ambNodes) {
			if (node instanceof ClassInstanceCreation) {
				ClassInstanceCreation cic = (ClassInstanceCreation) node;
				PPABindingsUtil.fixConstructor(cic, typeRegistry, resolver,
						indexer, engine, true, false);
			}
		}
	}

	private boolean isUnknownMethod(IBinding binding) {
		boolean unknownMethod = false;

		if (isMethod(binding)) {
			IMethodBinding mBinding = (IMethodBinding) binding;
			ITypeBinding tBinding = mBinding.getReturnType();
			unknownMethod = PPABindingsUtil.isUnknownType(tBinding);
		}

		return unknownMethod;
	}

	private boolean isMethod(IBinding binding) {
		return binding != null && binding instanceof IMethodBinding;
	}

	private boolean isField(IBinding binding) {
		boolean isField = false;

		if (binding != null && binding instanceof IVariableBinding) {
			isField = ((IVariableBinding) binding).isField();
		}

		return isField;
	}

	private boolean isUnknownField(IBinding binding) {
		boolean unknownField = false;
		if (binding != null && binding instanceof IVariableBinding) {
			IVariableBinding varBinding = (IVariableBinding) binding;
			unknownField = varBinding.isField()
					&& varBinding.getDeclaringClass().getQualifiedName()
							.equals(PPATypeRegistry.UNKNOWN_CLASS_FQN);
		}
		return unknownField;
	}

	private void processFields() {
		for (ASTNode node : ambNodes) {
			if (node instanceof SimpleName) {			
				SimpleName sName = (SimpleName) node;
				IBinding binding = null;
				try{
					binding = sName.resolveBinding();
				}catch(Exception e){
					
				}finally{
					if (isUnknownField(binding)) {
						tryToFixField(sName, (IVariableBinding) binding);
					}
				}
				
			}
		}
	}

	private void tryToFixField(SimpleName name, IVariableBinding binding) {
		ASTNode container = PPAASTUtil.getFieldContainer(name, true, false);
//		System.out.print("");
		ITypeBinding probableContainerType = getProbableContainerType(container);

		if (probableContainerType != null
				&& !probableContainerType.getQualifiedName().equals(
						PPATypeRegistry.UNKNOWN_CLASS_FQN)) {
			IVariableBinding newFieldBinding = typeRegistry.getFieldBinding(
					binding.getName(), probableContainerType,
					binding.getType(), resolver);
			resolver.fixFieldBinding(name, newFieldBinding);
		} else if (probableContainerType == null && container instanceof Name) {
			Name containerName = (Name) container;
			if (!isField(containerName.resolveBinding())) {
				String fqn = containerName.getFullyQualifiedName();
				ITypeBinding containerType = typeRegistry.getTypeBinding(
						(CompilationUnit) PPAASTUtil.getSpecificParentType(
								container, ASTNode.COMPILATION_UNIT), fqn,
						resolver, false, PPATypeBindingOptions.parseOptions(containerName));
				IVariableBinding newFieldBinding = typeRegistry
						.getFieldBinding(binding.getName(), containerType,
								binding.getType(), resolver);
				resolver.fixFieldBinding(name, newFieldBinding);
			} else {
				// We just uncovered a wrong container!
				// TODO Find a new suitable type
				// TODO Report this new type
			}
		}
		else{//zhh 
			ITypeBinding containerType = typeRegistry.getPossibleDeclaringType(name, typeTable.get("thisType"));
		
			if(container!=null&&binding!=null){
				IVariableBinding newFieldBinding = typeRegistry
						.getFieldBinding(binding.getName(), containerType,
								binding.getType(), resolver);
				resolver.fixFieldBinding(name, newFieldBinding);
			}
		}
	}

	private ITypeBinding getProbableContainerType(ASTNode container) {
		ITypeBinding binding = PPABindingsUtil
				.getFirstFieldContainerMissingSuperType(container);

		if (binding == null || PPABindingsUtil.isUnknownType(binding)) {
			// This is a workaround if the container is part of a qualified name.
			// The container may be obtained by looking at the declaring class of the field being fixed.
			// This will always return UNKNOWNP.UNKNOWN, which is obviously not good!!!
//			String shortname = container.toString(); //by nameng
//			ITypeBinding typeB = this.typeTable.get(shortname);
//			if(typeB!=null){
//				binding = typeB;
//				resolver.fixFQNType(container, typeB.getQualifiedName());
//			}	
			if (container instanceof Name) {
				Name name = (Name) container;
				IBinding iBinding = name.resolveBinding();
				if (iBinding instanceof IVariableBinding) {
					IVariableBinding varBinding = (IVariableBinding)iBinding;
					binding = varBinding.getType();
				}				
			}
		}
		//zhh
//		if(binding == null){
//			String shortname = container.toString();
//			ITypeBinding typeB = this.typeTable.get(shortname);
//			if(typeB!=null){
//				binding = typeB;
//				resolver.fixFQNType(container, typeB.getQualifiedName());
//			}		
//		}
		return binding;
	}

}
