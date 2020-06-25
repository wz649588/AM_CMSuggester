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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.SimpleName;

import ca.mcgill.cs.swevo.ppa.inference.ArrayAccessInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.AssignInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.BinaryInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.ConditionInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.ConditionalInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.ConstructorInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.FieldDeclarationStrategy;
import ca.mcgill.cs.swevo.ppa.inference.FieldInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.MethodInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.PostfixInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.PrefixInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.QNameInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.ReturnInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.SimpleNameInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.SwitchStatementInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.TypeInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.VariableDeclarationInferenceStrategy;
import ca.mcgill.cs.swevo.ppa.inference.VariableDeclarationStrategy;

public class PPAIndexer {

	public final static int FIELD_TYPE = 10001;

	public final static int LOCAL_TYPE = 10002;

	public final static int METHOD_TYPE = 10003;

	public final static int TYPE_TYPE = 10004;

	private final PPAEngine ppaEngine;

	private final Map<Integer, TypeInferenceStrategy> strategies = new HashMap<Integer, TypeInferenceStrategy>();

	public PPAIndexer(PPAEngine ppaEngine) {
		this.ppaEngine = ppaEngine;
		initStrategies();
	}

	private void initStrategies() {
		strategies.put(FIELD_TYPE, new FieldInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.ASSIGNMENT, new AssignInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.QUALIFIED_NAME, new QNameInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.RETURN_STATEMENT, new ReturnInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.VARIABLE_DECLARATION_FRAGMENT,
				new VariableDeclarationInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.METHOD_INVOCATION, new MethodInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.SUPER_METHOD_INVOCATION, new MethodInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.WHILE_STATEMENT, new ConditionInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.DO_STATEMENT, new ConditionInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.IF_STATEMENT, new ConditionInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.INFIX_EXPRESSION, new BinaryInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.ARRAY_ACCESS, new ArrayAccessInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.PREFIX_EXPRESSION, new PrefixInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.POSTFIX_EXPRESSION, new PostfixInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.CLASS_INSTANCE_CREATION, new ConstructorInferenceStrategy(this,
				ppaEngine));
		strategies.put(ASTNode.CONDITIONAL_EXPRESSION, new ConditionalInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.FOR_STATEMENT, new ConditionInferenceStrategy(this, ppaEngine));
		
		
		strategies.put(ASTNode.SWITCH_STATEMENT, new SwitchStatementInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.SIMPLE_NAME, new SimpleNameInferenceStrategy(this, ppaEngine));
		strategies.put(ASTNode.VARIABLE_DECLARATION_STATEMENT, new VariableDeclarationStrategy(this, ppaEngine));
		strategies.put(ASTNode.FIELD_DECLARATION, new FieldDeclarationStrategy(this, ppaEngine));
		
	}

	public int getNodeType(ASTNode node) {
		int type = node.getNodeType();

		if (type == ASTNode.SIMPLE_NAME) {
			SimpleName sName = (SimpleName) node;
			try{
				IBinding binding = sName.resolveBinding();
				if (binding != null) {
					if (binding instanceof IVariableBinding) {
						IVariableBinding varBinding = (IVariableBinding) binding;
						if (varBinding.isField()) {
							type = FIELD_TYPE;
						} else {
							type = LOCAL_TYPE;
						}
					} else if (binding instanceof IMethodBinding) {
						type = METHOD_TYPE;
					} else if (binding instanceof ITypeBinding) {
						type = TYPE_TYPE;
					}
				}
			}catch(Exception e){
				System.out.println("Error in sName.resolveBinding();");
				exdist.ExceptionHandler.process(e, "Error in sName.resolveBinding();");
			}
		}

		return type;
	}

	public boolean isIndexable(ASTNode node) {
		int type = getNodeType(node);

		return strategies.containsKey(type);
	}

	public PPAIndex getMainIndex(ASTNode node) {
		PPAIndex index = null;

		int type = getNodeType(node);

		if (strategies.containsKey(type)) {
			index = strategies.get(type).getMainIndex(node);
		}

		assert index != null;

		return index;
	}

	public List<PPAIndex> getSecondaryIndexes(ASTNode node) {
		List<PPAIndex> indexes = null;

		int type = getNodeType(node);

		if (strategies.containsKey(type)) {
			indexes = strategies.get(type).getSecondaryIndexes(node);
		}

		assert indexes != null;

		return indexes;
	}

	public List<PPAIndex> getAllIndexes(ASTNode node) {
		List<PPAIndex> indexes = new ArrayList<PPAIndex>();
		indexes.add(getMainIndex(node));
		indexes.addAll(getSecondaryIndexes(node));
		return indexes;
	}

	public boolean hasDeclaration(ASTNode node) {
		boolean isSafe = true;

		if (node != null) {
			int type = getNodeType(node);

			if (strategies.containsKey(type)) {
				isSafe = strategies.get(type).hasDeclaration(node);
			}
		}
		return isSafe;
	}

	public boolean isSafe(ASTNode node) {
		boolean isSafe = true;

		if (node != null) {
			int type = getNodeType(node);

			if (strategies.containsKey(type)) {
				TypeInferenceStrategy strategy = strategies.get(type);
				isSafe = strategy.isSafe(node);
			}
		}
		return isSafe;
	}

	public void inferTypes(ASTNode node) {
		int type = getNodeType(node);

		if (strategies.containsKey(type)) {
			strategies.get(type).inferTypes(node);
		} else {
			assert false;
		}
	}

	public void makeSafe(ASTNode node, TypeFact typeFact) {
		int type = getNodeType(node);

		if (strategies.containsKey(type)) {
			TypeInferenceStrategy strategy = strategies.get(type);
			if (!strategy.isSafe(node)) {
				TypeInferenceStrategy tStrategy = strategies.get(type);//split into two statements by nameng
				tStrategy.makeSafe(node, typeFact); // to facilitate debugging
			}
		} else {
			assert false;
		}
	}

	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		int type = getNodeType(node);

		if (strategies.containsKey(type)) {
			strategies.get(type).makeSafeSecondary(node, typeFact);
		} else {
			assert false;
		}
	}

}
