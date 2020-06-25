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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.lookup.PPATypeBindingOptions;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

/**
 * <p>This visitor determines the kind of ambiguous syntax construct (like field vs. type).</p>
 * 
 * @author Barthelemy Dagenais
 *
 */
public class SyntaxDisambiguation extends ASTVisitor {

	private PPADefaultBindingResolver ppaResolver;

	private Set<ASTNode> ambNodes = new HashSet<ASTNode>();

	private Map<ASTNode, Map<String, List<Name>>> ambiguousFieldsTypes = new HashMap<ASTNode, Map<String, List<Name>>>();

	private Set<Name> ambiguousMethods = new HashSet<Name>();

	private Set<Name> ambiguousParameterizedTypes = new HashSet<Name>();	

	private Map<ASTNode, Map<String, AmbiguousFQNNodes>> ambiguousFQNs = new HashMap<ASTNode, Map<String, AmbiguousFQNNodes>>();
	
//	private ArrayList<String> declaredFields = new ArrayList<String>();//commented by nameng
	private Map<String, IVariableBinding> declaredFields = new HashMap<String, IVariableBinding>(); 
	
	private ArrayList<String> declaredMethods = new ArrayList<String>();
	
	public Hashtable<String, ITypeBinding> typeTable = null; //added by nameng

	@Override
	public void endVisit(FieldDeclaration node) {
		// TODO Auto-generated method stub
		for(int i=0; i<node.fragments().size(); i++){
			Object o = node.fragments().get(i);
			if(o instanceof VariableDeclarationFragment){
				VariableDeclarationFragment vd = (VariableDeclarationFragment)o;
				declaredFields.put(vd.getName().getFullyQualifiedName(), vd.resolveBinding());//modified by nameng to add IVariableBinding
			}
		}
		super.endVisit(node);
	}

	public SyntaxDisambiguation(PPADefaultBindingResolver ppaResolver) {
		super();
		this.ppaResolver = ppaResolver;
	}

	private void addAmbiguousFieldType(SimpleName node) {
		// TODO Identifying the correct container is MIGHTY important
		ASTNode container = PPAASTUtil.getFieldContainer(node, true, false);	
		Map<String, List<Name>> ambiguousNodes = ambiguousFieldsTypes.get(container);
		if (ambiguousNodes == null) {
			ambiguousNodes = new HashMap<String, List<Name>>();
			ambiguousFieldsTypes.put(container, ambiguousNodes);
		}

		String nameKey = PPAASTUtil.getQualifierPlusName(node);
		List<Name> nodes = ambiguousNodes.get(nameKey);
		if (nodes == null) {
			nodes = new ArrayList<Name>();
			ambiguousNodes.put(nameKey, nodes);
		}
		nodes.add(node);
		this.ambNodes.add(node);
	}

//	@Override
//	public void endVisit(CastExpression node) {//added by nameng
//		if (ppaResolver.isProblematicBinding(node.resolveTypeBinding())) {
//			ppaResolver.fixCast(node);
//		}
//	}

	@Override
	public void endVisit(MethodDeclaration node) {
		this.declaredMethods.add(node.getName().getFullyQualifiedName());
		if (ppaResolver.isProblematicBinding(node)) {
			ppaResolver.fixMethodDeclaration(node);
		}
	}

	@Override
	public void endVisit(SimpleType node) {
//		System.out.println("SimpleType:"+node.getName());
		if (ppaResolver.isProblematicBinding(node)) {
			ppaResolver.fixSimpleType(node);
		}
	}

	@Override
	public void endVisit(ClassInstanceCreation node) {
		if (ppaResolver.isProblematicBinding(node)) {
			ppaResolver.fixClassInstanceCreation(node);
			this.ambNodes.add(node);
		}
		
	}
	
	@Override
	public void endVisit(SimpleName node){
		
		// Debug Ye Wang
		/*
		Object oldAst = ppaResolver.newAstToOldAst.get(node);
		IBinding binding = node.resolveBinding();
		ASTNode parent = node.getParent();
		
		boolean isParameter;
		boolean isEnumConstant;
		boolean isField;
		if (binding instanceof IVariableBinding) {
			isParameter = ((IVariableBinding) binding).isParameter();
			isEnumConstant = ((IVariableBinding) binding).isEnumConstant();
			isField = ((IVariableBinding) binding).isField();
			System.out.println();
		}
		
		
		
		if (ppaResolver.isSimpleNameRef(node)) {
			ppaResolver.isSimpleNameRef(node);
		}
		if (ppaResolver.isQualifiedNameReference(node)) {
			ppaResolver.isQualifiedNameReference(node);
		}
		if (ppaResolver.isFieldReference(node)) {
			ppaResolver.isFieldReference(node);
		}
		*/
		// ---
		
		
		
		if (ppaResolver.isProblematicBinding(node) || PPAASTUtil.isUnsafeMethod(node)) {
			if (ppaResolver.isParameterizedSingleTypeRef(node)) {
				ambiguousParameterizedTypes.add(node);
			} else if (ppaResolver.isSingleTypeRef(node)) {
				ppaResolver.fixSingleTypeRef(node);
			} else if (ppaResolver.isQualifiedTypeReference(node)) {
				ppaResolver.fixQualifiedTypeReference(node);
			} else if (ppaResolver.isLocalDeclaration(node)) {
				ppaResolver.fixLocal(node);
			} else if (ppaResolver.isSimpleNameRef(node)
					|| ppaResolver.isQualifiedNameReference(node)
					|| ppaResolver.isFieldReference(node)) {
				if (!LocalVariableUtil.isLocalVariable(node)) // adde by Ye Wang, to fix a bug, 02/09/2018
					addAmbiguousFieldType(node);
			} else if (ppaResolver.isMessageSend(node)) {
				ambiguousMethods.add(node);
			}
		} 
//		else { //commented by nameng: seems useless--If there is no problem resolve binding, no need to add it to ambiguousFQNs
//			ASTNode parent = node.getParent();
//			if ((ppaResolver.isSimpleNameRef(node) || ppaResolver.isQualifiedNameReference(node) || ppaResolver
//					.isFieldReference(node))
//					&& parent instanceof QualifiedName) {
//				if (PPABindingsUtil.getSafetyValue(node.resolveTypeBinding()) < PPABindingsUtil.FULL_TYPE) {
//
//					ASTNode container = PPAASTUtil.getFieldContainer(node, true, false);
//					IBinding binding = node.resolveBinding();
//					if (binding != null && binding instanceof IVariableBinding) {
//						addToAmbiguousFQNs(container, node.getFullyQualifiedName(), node,
//								(IVariableBinding) binding);
//					}
//				}
//			}
//		}

		super.endVisit(node);
	}

	public void postProcess(Map<String, IVariableBinding> declaredFields) {
//		Map<ASTNode, Map<String, List<Name>>> toVisit = new HashMap<ASTNode, Map<String, List<Name>>>();
		for (ASTNode container : ambiguousFieldsTypes.keySet()) {
			Map<String, List<Name>> ambiguousNodes = ambiguousFieldsTypes.get(container);			
			for (String name : ambiguousNodes.keySet()) {
				List<Name> nodes = ambiguousNodes.get(name);
				
				// Debug Ye Wang
//				for (Name node: nodes) {
//					if (node.getParent().toString().contains("isDigestQuery"))
//						System.out.println(node.getParent());
//				}
				// ---
				
				if(declaredFields.containsKey(name)){//modified by nameng
					addFieldBinding2(container, name, nodes);//commented by nameng
				}else {					
					if (!PPAASTUtil.isIndicationOfField(nodes, typeTable)) {//typeTable parameter added by nameng
						addTypeBinding(container, name, nodes);
					} else {
//						if (typeTable.containsKey(container.toString())) {//added by nameng
//							PPATypeRegistry typeRegistry = ppaResolver.getTypeRegistry();
//							IVariableBinding fieldBinding = typeRegistry.getFieldBinding(name, typeTable.get(container.toString()), 
//									typeRegistry.getUnknownBinding(ppaResolver), ppaResolver);
//							for (Name node : nodes) {
//								ppaResolver.fixFieldBinding(node, fieldBinding);
//							}
//						} else {
							addFieldBinding(container, name, nodes);
//						}
//						Map<String, List<Name>> values = toVisit.get(container); //added by nameng
//						if (values == null) {
//							values = new HashMap<String, List<Name>>();
//							toVisit.put(container, values);
//						}
//						values.put(name, nodes);
					}
				}					
//					if (!PPAASTUtil.isIndicationOfField(nodes)) {
//					addTypeBinding(container, name, nodes);
//				} else {
////					addFieldBinding(container, name, nodes);
//					Map<String, List<Name>> values = toVisit.get(container); //added by nameng
//					if (values == null) {
//						values = new HashMap<String, List<Name>>();
//						toVisit.put(container, values);
//					}
//					values.put(name, nodes);
//				}
			}
		}

//		for (ASTNode container : toVisit.keySet()) {
//			Map<String, List<Name>> ambiguousNodes = toVisit.get(container);
//			for (String name : ambiguousNodes.keySet()) {
//				List<Name> nodes = ambiguousNodes.get(name);				
//				addFieldBinding(container, name, nodes);
//			}
//		}
		
		// Debug Ye Wang
//		TestVisitor tv = new TestVisitor();
//		PPAEngine.currentCU.accept(tv);
		// ---

		
		processAmbiguousFQN();

		// Type parameters must be fixed before fixing the container type,
		// hence the reason why they are processed at the end.
		for (Name name : ambiguousParameterizedTypes) {
			ppaResolver.fixParameterizedSingleTypeRef(name);
		}
		
		for (Name name : ambiguousMethods) {
			ASTNode parent = name.getParent();
			if(parent instanceof MethodInvocation){
				MethodInvocation mi = (MethodInvocation)parent;
				if(mi.getExpression()==null){
//					if(!this.declaredMethods.contains(fullname)){
						ppaResolver.fixMessageSend(name);
						this.ambNodes.add(name);
//					}
				}
				else{
//					ppaResolver.fixMessageSend(name);zhh
					IBinding nameB = name.resolveBinding();
					if(nameB==null){
						ppaResolver.fixMessageSend(name);
					}
					this.ambNodes.add(name);
				}
			}else if(parent instanceof SuperMethodInvocation){
//					ppaResolver.fixMessageSend(name);zhh
				IBinding nameB = name.resolveBinding();
				if(nameB==null){
					ppaResolver.fixMessageSend(name);
				}
				this.ambNodes.add(name);
			}
		}
	}

	private void processAmbiguousFQN() {
		for (ASTNode container : ambiguousFQNs.keySet()) {
			Map<String, AmbiguousFQNNodes> map = ambiguousFQNs.get(container);
			List<Map.Entry<String, AmbiguousFQNNodes>> list = getOrderedListFromMap(map);
			processOrderedFQNList(list);
		}
	}

	private void processOrderedFQNList(List<Entry<String, AmbiguousFQNNodes>> list) {
		String current = "-1";
		// String previous = "-1";
		int size = list.size();
		Map.Entry<String, AmbiguousFQNNodes> currentEntry;
		IVariableBinding previousBinding = null;
		PPATypeRegistry typeRegistry = ppaResolver.getTypeRegistry();
		boolean lastOfItsKind = false;
		Map<String, IVariableBinding> previousBindings = new HashMap<String, IVariableBinding>();
		for (int i = 0; i < size; i++) {

			currentEntry = list.get(i);
			// previous = current;
			current = currentEntry.getKey();
			// CompilationUnit cu =
			// (CompilationUnit)PPAUtil.getSpecificParentType
			// (currentEntry.getValue
			// ().getNodes().get(0),ASTNode.COMPILATION_UNIT);

			// TODO: BUG! In fact, the sort is not good! Arg!
			// z1.z2 = z1.z3.z4
			// z1
			// then z2
			// then z3 (previous is z1.z2);
			// if (isNewKind(current, previous)) {
			// previousBinding = null;
			// }
			previousBinding = getPreviousBinding(current, previousBindings);
			lastOfItsKind = lastOfItsKind(list, i);

			if (lastOfItsKind && !currentEntry.getValue().isField() && previousBinding == null) {
				for (ASTNode node : currentEntry.getValue().getNodes()) {
					ppaResolver.fixFQNType(node, current);
				}
			} else if (previousBinding != null) {
				// IVariableBinding entryBinding =
				// currentEntry.getValue().getFieldBinding();
				// ITypeBinding containerType = previousBinding.getType();
				// ITypeBinding fieldType = (entryBinding == null ||
				// entryBinding.getType() == null) ? typeRegistry
				// .getUnknownBinding(ppaResolver)
				// : entryBinding.getType();
				IVariableBinding newBinding = typeRegistry.getUnknownFieldBinding(PPABindingsUtil
						.getSimpleName(current).toCharArray(), ppaResolver);

				for (ASTNode node : currentEntry.getValue().getNodes()) {
					ppaResolver.fixFQNField(node, newBinding, current, lastOfItsKind);
				}

				previousBindings.put(currentEntry.getKey(), newBinding);
			} else if (currentEntry.getValue().isField()) {
				// IVariableBinding entryBinding =
				// currentEntry.getValue().getFieldBinding();
				// ITypeBinding containerType =
				// entryBinding.getDeclaringClass();
				//
				// if (containerType == null ||
				// PPAUtil.isUnknownType(containerType)) {
				// containerType = typeRegistry.getTypeBinding(cu,
				// PPAUtil.getPackage(current),
				// ppaResolver);
				// }
				// ITypeBinding fieldType = entryBinding.getType() == null ?
				// typeRegistry
				// .getUnknownBinding(ppaResolver) : entryBinding.getType();
				
				List<ASTNode> nodes = currentEntry.getValue().getNodes();
				
				IVariableBinding newBinding = null;
				newBinding = typeRegistry.getUnknownFieldBinding(PPABindingsUtil
							.getSimpleName(current).toCharArray(), ppaResolver);
					
				for (ASTNode node : nodes) {
					ppaResolver.fixFQNField(node, newBinding, current, lastOfItsKind);
				}
				previousBindings.put(currentEntry.getKey(), newBinding);
			}

		}
	}

	private IVariableBinding getPreviousBinding(String current,
			Map<String, IVariableBinding> previousBindings) {
		IVariableBinding varBinding = null;
		int index = current.lastIndexOf('.');
		if (index != -1) {
			String parent = current.substring(0, index);
			varBinding = previousBindings.get(parent);
		}
		return varBinding;
	}

	/**
	 * <p>
	 * If the previous FQN is not the prefix of the current FQN, the current FQN is a new kind.
	 * </p>
	 * 
	 * @param current
	 * @param previous
	 * @return
	 */
	// private boolean isNewKind(String current, String previous) {
	// return !current.startsWith(previous);
	// }
	/**
	 * <p>
	 * If the current FQN is not the prefix of the next one, it is the last of its kind.
	 * </p>
	 * 
	 * @param list
	 * @param currentFQN
	 * @param currentIndex
	 * @return
	 */
	private boolean lastOfItsKind(List<Entry<String, AmbiguousFQNNodes>> list, int currentIndex) {
		boolean lastOfItsKind = true;

		if (list.size() > currentIndex + 1) {
			lastOfItsKind = !list.get(currentIndex + 1).getKey().startsWith(
					list.get(currentIndex).getKey());
		}

		return lastOfItsKind;
	}

	private List<Map.Entry<String, AmbiguousFQNNodes>> getOrderedListFromMap(
			Map<String, AmbiguousFQNNodes> map) {
		List<Map.Entry<String, AmbiguousFQNNodes>> list = new ArrayList<Entry<String, AmbiguousFQNNodes>>(
				map.entrySet());
		Collections.sort(list, new AmbiguousFQNsComparator());
		return list;
	}

	private void addFieldBinding(ASTNode container, String name, List<Name> nodes) {
		PPATypeRegistry typeRegistry = ppaResolver.getTypeRegistry();
		IVariableBinding fieldBinding = typeRegistry.getUnknownFieldBinding(name.toCharArray(),
				ppaResolver);
		;

		// ITypeBinding probableContainerType = PPAUtil
		// .getFirstFieldContainerMissingSuperType(container);

		for (Name node : nodes) {
			if (node.getParent() instanceof QualifiedName ) {				
					addToAmbiguousFQNs(container, name, node, fieldBinding);
			} else {
				ppaResolver.fixFieldBinding(node, fieldBinding);
			}
		}
	}
	
	private void addFieldBinding2(ASTNode container, String name, List<Name> nodes) {
		IVariableBinding fieldBinding = declaredFields.get(name);
		for (Name node : nodes) {
//			if (node.getParent() instanceof QualifiedName ) {
//				addToAmbiguousFQNs(container, name, node, fieldBinding);
//			} else {
				ppaResolver.fixFieldBinding(node, fieldBinding);
//			}
		}
	}

	private void addTypeBinding(ASTNode container, String name, List<Name> nodes) {
		CompilationUnit cu = (CompilationUnit) PPAASTUtil.getSpecificParentType(nodes.get(0),
				ASTNode.COMPILATION_UNIT);
		PPATypeRegistry typeRegistry = ppaResolver.getTypeRegistry();
		PPATypeBindingOptions options = new PPATypeBindingOptions();
		if (nodes.size() > 0) {
			options = PPATypeBindingOptions.parseOptions(nodes.get(0));
		}
		ITypeBinding tBinding = typeRegistry.getTypeBinding(cu, name, ppaResolver, false, options);
		for (Name node : nodes) {
			ASTNode parent = node.getParent();//added by nameng
			if (parent instanceof QualifiedName) {		
				addToAmbiguousFQNs(container, name, node, null);
				ppaResolver.fixQualifiedTypeBinding(node, tBinding);
			} else { 
				ppaResolver.fixTypeBinding(node, tBinding);
			}
		}
	}

	private void addToAmbiguousFQNs(ASTNode container, String name, Name node,
			IVariableBinding fieldBinding) {		
		ASTNode newContainer = PPAASTUtil.getFieldContainer(container, false, true);
		
		Map<String, AmbiguousFQNNodes> map = ambiguousFQNs.get(newContainer);
		if (map == null) {
			map = new HashMap<String, AmbiguousFQNNodes>();
			ambiguousFQNs.put(newContainer, map);
		}

		AmbiguousFQNNodes nodes = map.get(name);
		if (nodes == null) {
			nodes = new AmbiguousFQNNodes();
			map.put(name, nodes);
		}

		if (fieldBinding != null) {
			// Only overwrite if true
			nodes.setFieldBinding(fieldBinding);
		}
		nodes.getNodes().add(node);
	}

	public Set<ASTNode> getAmbiguousNodes() {
		return ambNodes;
	}

	public Map<String, IVariableBinding> getDeclaredFields() {
		// TODO Auto-generated method stub
		return this.declaredFields;
	}

}

class AmbiguousFQNNodes {

	private List<ASTNode> nodes = new ArrayList<ASTNode>();

	private IVariableBinding fieldBinding;

	public boolean isField() {
		return fieldBinding != null;
	}

	public List<ASTNode> getNodes() {
		return nodes;
	}

	public void setNodes(List<ASTNode> nodes) {
		this.nodes = nodes;
	}

	public IVariableBinding getFieldBinding() {
		return fieldBinding;
	}

	public void setFieldBinding(IVariableBinding fieldBinding) {
		if (this.fieldBinding == null) {
			this.fieldBinding = fieldBinding;
		}
	}

}

class AmbiguousFQNsComparator implements Comparator<Map.Entry<String, AmbiguousFQNNodes>> {

	public int compare(Entry<String, AmbiguousFQNNodes> o1, Entry<String, AmbiguousFQNNodes> o2) {
		return o1.getKey().compareTo(o2.getKey());
	}

}
