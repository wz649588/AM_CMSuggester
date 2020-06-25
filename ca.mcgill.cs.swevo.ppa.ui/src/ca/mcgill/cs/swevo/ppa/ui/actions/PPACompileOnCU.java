package ca.mcgill.cs.swevo.ppa.ui.actions;

import java.io.File;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Shell;
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

public class PPACompileOnCU implements IObjectActionDelegate {

	private ICompilationUnit icu = null;

	public PPACompileOnCU() {
	}

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	public void run(IAction action) {
		if (icu == null) {
			return;
		}

		try {
			MessageConsole mConsole = new MessageConsole("PPA Console", null);
			final PrintStream printer = new PrintStream(mConsole.newMessageStream());
			IConsoleManager manager = ConsolePlugin.getDefault().getConsoleManager();
			manager.addConsoles(new IConsole[] { mConsole });
			manager.showConsoleView(mConsole);
			Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
			DirectoryDialog dDialog = new DirectoryDialog(shell);
			dDialog.setMessage("Choose a directory where the .class files will be saved.");
			dDialog.setText("Choose base directory");
			final String path = dDialog.open();

			ProgressMonitorDialog dialog = new ProgressMonitorDialog(shell);
			dialog.run(true, false, new IRunnableWithProgress() {

				public void run(IProgressMonitor monitor) throws InvocationTargetException,
						InterruptedException {
					try {
						monitor.beginTask("Visiting AST", 100);
						ASTNode node = PPAUtil.getCU((IFile) icu.getResource(), new PPAOptions(), false);
						monitor.worked(50);
						node.accept(new NameBindingVisitor(printer, monitor));
						printer.close();
						
						PPAUtil.compileCU((CompilationUnit)node, new File(path));
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
