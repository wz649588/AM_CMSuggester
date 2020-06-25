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
package ca.mcgill.cs.swevo.ppa.ui.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jdt.internal.ui.javaeditor.JavaTextSelection;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;

import ca.mcgill.cs.swevo.ppa.PPANameVisitor;
import ca.mcgill.cs.swevo.ppa.PPAOptions;
import ca.mcgill.cs.swevo.ppa.ui.PPAUtil;

@SuppressWarnings("restriction")
public class PPAOnNameAction implements IEditorActionDelegate {

	private ITextSelection selection;

	private JavaEditor javaEditor;

	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		if (targetEditor instanceof JavaEditor) {
			javaEditor = (JavaEditor) targetEditor;
		}
	}

	public void run(IAction action) {
		if (javaEditor != null) {
			ICompilationUnit icu = (ICompilationUnit) SelectionConverter.getInput(javaEditor);
			IDocument document = JavaUI.getDocumentProvider().getDocument(
					javaEditor.getEditorInput());
			JavaTextSelection javaSelection = new JavaTextSelection(icu, document, selection
					.getOffset(), selection.getLength());
			ASTNode[] nodes = javaSelection.resolveSelectedNodes();

			if (nodes != null && nodes.length == 1) {
				ASTNode node = nodes[0];
				if (node instanceof Name) {

					// 1- Get the PPA CU:
					CompilationUnit cu = PPAUtil.getCU((IFile) icu.getResource(), new PPAOptions());
					if (cu == null) {
						return;
					}
					PPANameVisitor nameVisitor = new PPANameVisitor();
					cu.accept(nameVisitor);

					// 2- Get the corresponding name in the PPA CU
					Name ppaNode = nameVisitor.getName((Name) node);
					if (ppaNode != null) {
						String bindingText = PPABindingsUtil.getBindingText(ppaNode
								.resolveBinding());
						MessageDialog.openInformation(javaEditor.getEditorSite().getShell(),
								"Binding for " + ppaNode.getFullyQualifiedName(), bindingText);
					}

					// 3- Clean-up
					PPAUtil.cleanUp(cu);
				}
			}
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof ITextSelection) {
			this.selection = (ITextSelection) selection;
		}

	}

}
