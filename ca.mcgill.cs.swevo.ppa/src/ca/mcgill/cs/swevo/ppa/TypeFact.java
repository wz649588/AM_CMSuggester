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
import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;


public class TypeFact implements Cloneable {



	public static int EQUALS = 0;

	public static int SUBTYPE = 1;

	public static int SUPERTYPE = 2;

	public static int RELATED = 3;

	public static int UNKNOWN = 4;

	public static final String VAR_STRATEGY = "VAR_STRATEGY";
	
	public static String ASSIGN_STRATEGY = "ASSIGN_STRATEGY";

	public static String RETURN_STRATEGY = "RETURN_STRATEGY";

	public static String METHOD_STRATEGY = "METHOD_STRATEGY";

	public static String CONDITION_STRATEGY = "CONDITION_STRATEGY";

	public static String BINARY_STRATEGY = "BINARY_STRATEGY";

	public static String UNARY_STRATEGY = "UNARY_STRATEGY";

	public static String ARRAY_STRATEGY = "ARRAY_STRATEGY";

	public static String SWITCH_STRATEGY = "SWITCH_STRATEGY";

	public static String CONDITIONAL_STRATEGY = "CONDITIONAL_STRATEGY";

	public static String FIELD_STRATEGY = "FIELD_STRATEGY";

	private PPAIndex index;

	private int oldDirection;

	private ITypeBinding oldType;

	private int newDirection;

	private ITypeBinding newType;

	private TypeFact origin;

	private String strategy;

	private List<TypeFact> constraints = new ArrayList<TypeFact>();

	boolean sound = true;

	// boolean propagation = false;

	public TypeFact(PPAIndex index, ITypeBinding oldType, int oldDirection, ITypeBinding newType,
			int newDirection, String strategy) {
		super();
		this.index = index;
		this.oldType = oldType;
		this.oldDirection = oldDirection;
		this.newType = newType;
		this.newDirection = newDirection;
		this.strategy = strategy;
	}

	public TypeFact(PPAIndex node, ITypeBinding oldType, int oldDirection, ITypeBinding newType,
			int newDirection, String strategy, TypeFact origin) {
		super();
		this.index = node;
		this.oldType = oldType;
		this.oldDirection = oldDirection;
		this.newType = newType;
		this.newDirection = newDirection;
		this.origin = origin;
		this.strategy = strategy;
	}

	public PPAIndex getIndex() {
		return index;
	}

	// public void setIndex(PPAIndex index) {
	// this.index = index;
	// }

	public int getOldDirection() {
		return oldDirection;
	}

	// public void setOldDirection(int oldDirection) {
	// this.oldDirection = oldDirection;
	// }

	public ITypeBinding getOldType() {
		return oldType;
	}

	// public void setOldType(ITypeBinding oldType) {
	// this.oldType = oldType;
	// }

	public int getNewDirection() {
		return newDirection;
	}

	// public void setNewDirection(int newDirection) {
	// this.newDirection = newDirection;
	// }

	public ITypeBinding getNewType() {
		return newType;
	}

	 public void setNewType(ITypeBinding newType) {
		this.newType = newType;
	}

	public TypeFact getOrigin() {
		return origin;
	}

	// public void setOrigin(TypeFact origin) {
	// this.origin = origin;
	// }

	public String getStrategy() {
		return strategy;
	}

	// public void setStrategy(String strategy) {
	// this.strategy = strategy;
	// }

	public List<TypeFact> getConstraints() {
		return constraints;
	}

	// public void setConstraints(List<TypeFact> constraints) {
	// this.constraints = constraints;
	// }

	public void addConstraint(TypeFact constraint) {
		constraints.add(constraint);
	}

	public boolean isSound() {
		return sound;
	}

	public void setSound(boolean sound) {
		this.sound = sound;
	}

	// public boolean isPropagation() {
	// return propagation;
	// }
	//
	// public void setPropagation(boolean propagation) {
	// this.propagation = propagation;
	// }

	@Override
	public String toString() {
		StringBuffer sBuffer = new StringBuffer();
		sBuffer.append(strategy);
		sBuffer.append(":");
		sBuffer.append(oldType);
		sBuffer.append("->");
		sBuffer.append(newType);
		return sBuffer.toString();
	}

	@Override
	public Object clone() {
		TypeFact tFact = null;
		try {
			tFact = (TypeFact) super.clone();
		} catch (Exception e) {
			e.printStackTrace();
			exdist.ExceptionHandler.process(e);
		}

		return tFact;
	}

}
