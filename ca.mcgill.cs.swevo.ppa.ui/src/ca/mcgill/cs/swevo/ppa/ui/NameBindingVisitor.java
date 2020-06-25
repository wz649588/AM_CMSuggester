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
package ca.mcgill.cs.swevo.ppa.ui;

import java.io.PrintStream;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;


/**
 * <p>
 * Visitor that prints the binding of each name it visits. This is the class
 * used by the various PPA actions.
 * </p>
 * 
 * @deprecated Use ca.mcgill.cs.swevo.ppa.util.NameBindingVisitor
 * @author Barthelemy Dagenais
 * 
 */
public class NameBindingVisitor extends ASTVisitor {

	private PrintStream printer;

	private IProgressMonitor monitor;

	public NameBindingVisitor(PrintStream printer, IProgressMonitor monitor) {
		super();
		this.printer = printer;
		this.monitor = monitor;
	}

	public NameBindingVisitor(PrintStream printer) {
		super();
		this.printer = printer;
		this.monitor = new NullProgressMonitor();
	}

	@Override
	public void postVisit(ASTNode node) {
		super.postVisit(node);
		ITypeBinding tBinding = null;
		IBinding binding = null;
		boolean isStatic = false;

		if (node instanceof Expression) {
			Expression exp = (Expression) node;

			if (exp instanceof Name) {
				Name name = (Name) exp;
				binding = name.resolveBinding();
			} else if (exp instanceof MethodInvocation) {
				MethodInvocation mi = (MethodInvocation) exp;
				IMethodBinding mBinding = mi.resolveMethodBinding();
				isStatic = Modifier.isStatic(mBinding.getModifiers());
				binding = mBinding;
			} else if (exp instanceof ClassInstanceCreation) {
				ClassInstanceCreation cic = (ClassInstanceCreation) exp;
				binding = cic.resolveConstructorBinding();
			} else {
				return;
			}
			tBinding = exp.resolveTypeBinding();
		} else if (node instanceof SuperConstructorInvocation) {
			SuperConstructorInvocation sci = (SuperConstructorInvocation) node;
			binding = sci.resolveConstructorBinding();
		} else if (node instanceof MethodDeclaration) {
			MethodDeclaration md = (MethodDeclaration) node;
			printer.println("METHOD DECLARATION: " + md.getName());
			if (md.getBody() != null) {
				printer.println(md.getBody().statements().size());
			}
		}
		if (binding != null) {
			printer.println("Node: " + node.toString());

			if (tBinding != null) {
				printer.println("  Type Binding: "
						+ tBinding.getQualifiedName());
				printer.println("  isAnnotation?: " + tBinding.isAnnotation());
			}

			if (binding != null) {
				printer.println("  " + PPABindingsUtil.getBindingText(binding));
			}

			printer.println("  isStatic?: " + isStatic);
			printer.flush();
			monitor.worked(1);
		}
	}

}
