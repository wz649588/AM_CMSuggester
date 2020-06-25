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

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;


public class PPAIndex {

	private ASTNode node;

	private IBinding binding;

	public PPAIndex(IBinding binding) {
		super();
		this.binding = binding;
	}

	public PPAIndex(ASTNode node) {
		super();
		this.node = node;
	}

	public ASTNode getNode() {
		return node;
	}

	public void setNode(ASTNode node) {
		this.node = node;
	}

	public IBinding getBinding() {
		return binding;
	}

	public void setBinding(IBinding binding) {
		this.binding = binding;
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof PPAIndex)) {
			return false;
		}
		PPAIndex other = (PPAIndex) arg0;

		if (node != null) {
			return other.node == node;
		} else if (other.binding == null) {
			return false;
		} else {
			// This is in case the binding partially changed.
			return PPABindingsUtil.isEquivalent(other.binding, binding);
		}

	}
	
	

	@Override
	public int hashCode() {
		if (node != null) {
			return node.hashCode();
		} else {
			return binding.getKey().hashCode();
		}
	}

}
