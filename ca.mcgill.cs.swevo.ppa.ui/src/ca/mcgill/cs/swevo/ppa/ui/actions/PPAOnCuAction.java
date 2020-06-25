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

import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;

import ca.mcgill.cs.swevo.ppa.PPAOptions;
import ca.mcgill.cs.swevo.ppa.util.NameBindingVisitor;
import ca.mcgill.cs.swevo.ppa.ui.PPAUtil;

public class PPAOnCuAction implements IObjectActionDelegate {

	private ICompilationUnit icu = null;
	
	public PPAOnCuAction() {
	}

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	public void run(IAction action) {
		if (icu == null) {
			return;
		}

		try {
			MessageConsole mConsole = new MessageConsole("PPA Console",null);
			final PrintStream printer = new PrintStream(mConsole.newMessageStream());
			IConsoleManager manager = ConsolePlugin.getDefault().getConsoleManager();
			manager.addConsoles(new IConsole[] {mConsole});
			manager.showConsoleView(mConsole);
			
			ProgressMonitorDialog dialog = new ProgressMonitorDialog(PlatformUI.getWorkbench()
					.getActiveWorkbenchWindow().getShell());
			dialog.run(true, false, new IRunnableWithProgress() {

				public void run(IProgressMonitor monitor) throws InvocationTargetException,
						InterruptedException {
					try {
						monitor.beginTask("Visiting AST", 100);
						ASTNode node = PPAUtil.getCU((IFile)icu.getResource(), new PPAOptions());
						monitor.worked(50);
						node.accept(new NameBindingVisitor(printer,monitor));
						printer.close();
					} catch (Exception e) {
						e.printStackTrace();
					} finally {
						monitor.done();
					}
				}
			});
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
		IStructuredSelection sSelection = (IStructuredSelection) selection;
		if (!sSelection.isEmpty()) {
			icu = (ICompilationUnit) sSelection.getFirstElement();
		}
	}
}
