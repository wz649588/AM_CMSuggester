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
 * 
 * Contributors:
 *     Puneet Kapur - 2009
 *******************************************************************************/
package ca.mcgill.cs.swevo.ppa.util;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTRequestor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.PPAASTParser;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.internal.compiler.ClassFile;
import org.eclipse.jdt.internal.core.JavaProject;

import ca.mcgill.cs.swevo.ppa.PPAOptions;
import ca.mcgill.cs.swevo.ppa.SnippetUtil;

/**
 * <p>
 * Collection of utility methods to get compilation units from partial programs.
 * </p>
 * 
 * @author Barthelemy Dagenais
 * 
 */
@SuppressWarnings("restriction")
public class PPACoreUtil {

	private final static Logger logger = Logger.getLogger(PPACoreUtil.class);

	public static void cleanUp(CompilationUnit cu, String requestName) {
		ICompilationUnit icu = (ICompilationUnit) cu.getJavaElement();
		IFile iFile = (IFile) icu.getResource();
		IProject project = iFile.getProject();
		if (project.equals(ResourcesPlugin.getWorkspace().getRoot()
				.getProject(getPPAProjectName(requestName)))) {
			try {
				PPACoreResourceUtil.cleanUp(iFile);
			} catch (CoreException ce) {
				logger.error("Error during file cleanup.", ce);
			} finally {
				PPACoreSingleton.getInstance().releaseId(requestName);
			}
		}
	}

	public static void cleanUp(CompilationUnit cu) {
		cleanUp(cu, Thread.currentThread().getName());
	}

	public static void cleanUpAll() {
		cleanUpAll(Thread.currentThread().getName());
	}

	public static void cleanUpAll(String requestName) {
		IProject project = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(getPPAProjectName(requestName));
		if (project.exists()) {
			int deleted = 0;
			IFolder src = project.getFolder("src");
			final List<IFile> toDelete = new ArrayList<IFile>();
			try {
				src.accept(new IResourceVisitor() {

					public boolean visit(IResource resource) throws CoreException {
						if (resource.getType() == IResource.FILE) {
							toDelete.add((IFile) resource);
						}
						return true;
					}

				});
			} catch (Exception e) {
				logger.error("Error while cleaning up PPA project", e);
			}

			for (IFile file : toDelete) {
				try {
					file.delete(true, new NullProgressMonitor());
					deleted++;
				} catch (Exception e) {
					logger.error("Error while cleaning up PPA project", e);
				}
			}
			PPACoreSingleton.getInstance().releaseId(requestName);
			// logger.info("DELETED: " + deleted + " files deleted out of " +
			// toDelete.size());
		}
	}

	public static void cleanUpSnippet(String requestName) {
		IProject project = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(getPPAProjectName(requestName));
		IFolder snippetFolder = project.getFolder("src").getFolder(SnippetUtil.SNIPPET_PACKAGE);
		IFile snippetFile = snippetFolder.getFile(SnippetUtil.SNIPPET_FILE);
		try {
			snippetFile.delete(true, new NullProgressMonitor());
			snippetFolder.delete(true, new NullProgressMonitor());
		} catch (CoreException ce) {
			logger.error("Error during file cleanup.", ce);
		} finally {
			PPACoreSingleton.getInstance().releaseId(requestName);
		}
	}

	public static void cleanUpSnippet() {
		cleanUpSnippet(Thread.currentThread().getName());
	}

	public static CompilationUnit getCU(String content, PPAOptions options, String requestName) {
		CompilationUnit cu = null;

		try {
			File temp = File.createTempFile(SnippetUtil.SNIPPET_CLASS, ".java");
			BufferedWriter out = new BufferedWriter(new FileWriter(temp));
			out.write(content);
			out.close();
			cu = getCU(temp, options, requestName);
			temp.delete();
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}
		return cu;
	}

	public static CompilationUnit getCU(String content, PPAOptions options) {
		return getCU(content, options, Thread.currentThread().getName());
	}

	public static CompilationUnit getCU(final File file, final PPAOptions options) {
		return getCU(file, options, Thread.currentThread().getName());
	}

	/**
	 * 
	 * @param file
	 * @param options
	 * @param requestName
	 * @param cleanupAfterParsing
	 *            Should be false if CU is compiled afterward.
	 * @return
	 */
	public static CompilationUnit getCU(File file, PPAOptions options, String requestName,
			boolean cleanupAfterParsing) {
		CompilationUnit cu = null;
		String fileName = file.getName();

		try {
			String packageName = getPackageFromFile(file);
			String ppaProjectName = getPPAProjectName(requestName);
			PPACoreJavaProjectHelper helper = new PPACoreJavaProjectHelper();
			IJavaProject javaProject = helper.setupJavaProject(ppaProjectName);
			IFile newFile = PPACoreResourceUtil.copyJavaSourceFile(javaProject.getProject(), file,
					packageName, fileName);
			cu = getCU(newFile, options, cleanupAfterParsing);
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}

		return cu;
	}

	public static CompilationUnit getCU(File file, PPAOptions options, String requestName) {
		return getCU(file, options, requestName, true);
	}

	public static CompilationUnit getCU(IFile file, PPAOptions options, boolean cleanupAfterParsing) {
		CompilationUnit cu = null;
		try {
			ICompilationUnit icu = JavaCore.createCompilationUnitFrom(file);
			PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
					.getUnderlyingResource().getProject()));
			ASTNode node = null;
			PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
			parser2.setStatementsRecovery(true);
			parser2.setResolveBindings(true);
			parser2.setSource(icu);
			node = parser2.createAST(cleanupAfterParsing, null);
			PPAEngine ppaEngine = new PPAEngine(registry, options);

			cu = (CompilationUnit) node;

			ppaEngine.addUnitToProcess(cu);
			ppaEngine.doPPA();
			ppaEngine.reset();

		} catch (JavaModelException jme) {
			// Retry with the file version.
			logger.warn("Warning while getting CU from PPA");
			logger.debug("Exception", jme);
			cu = getCU(file.getLocation().toFile(), options);
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}

		return cu;
	}

	public static CompilationUnit getCU(IFile file, PPAOptions options) {
		return getCU(file, options, true);
	}

	/**
	 * <p>
	 * Creates a ClassFile instance for each TypeDeclaration in the compilation unit.
	 * </p>
	 * <p>
	 * This method sets various flags to enable the Eclipse Java Compiler to work with PPA-generated
	 * compilation unit.
	 * </p>
	 * 
	 * @param cu
	 * @return
	 */
	public static ClassFile[] compileCU(CompilationUnit cu) {
		ClassFile[] classFiles = null;
		try {
			classFiles = PPABindingsUtil.compileCU(cu);
		} catch (Exception e) {
			logger.error("Error while compiling a PPA compilation unit.", e);
		}

		return classFiles;
	}

	/**
	 * <p>
	 * Creates a ClassFile instance for each TypeDeclaration in the compilation unit. Writes the
	 * resulting class files in the specified base directory.
	 * </p>
	 * <p>
	 * This method sets various flags to enable the Eclipse Java Compiler to work with PPA-generated
	 * compilation unit.
	 * </p>
	 * 
	 * @param cu
	 * @param baseDir
	 * @return
	 */
	public static ClassFile[] compileCU(CompilationUnit cu, File baseDir) {
		ClassFile[] classFiles = null;
		try {
			classFiles = PPABindingsUtil.compileCU(cu);
			for (ClassFile classFile : classFiles) {
				PPABindingsUtil.writeClassFile(classFile, baseDir);
			}
		} catch (Exception e) {
			logger.error("Error while compiling and writing a PPA compilation unit.", e);
		}

		return classFiles;
	}

	public static CompilationUnit getCUNoPPA(IFile file) {
		CompilationUnit cu = null;
		try {
			ICompilationUnit icu = JavaCore.createCompilationUnitFrom(file);
			ASTNode node = null;
			PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
			parser2.setStatementsRecovery(true);
			parser2.setResolveBindings(true);
			parser2.setSource(icu);
			node = parser2.createAST(true, null);
			cu = (CompilationUnit) node;
		} catch (Exception e) {
			logger.error("Error while getting CU without PPA", e);
		}

		return cu;
	}

	public static List<CompilationUnit> getCUs(final List<File> files, final PPAOptions options) {
		return getCUs(files, options, Thread.currentThread().getName());
	}

	public static List<CompilationUnit> getCUs(List<File> files, PPAOptions options,
			String requestName) {
		List<CompilationUnit> cus = new ArrayList<CompilationUnit>();
		List<IFile> iFiles = new ArrayList<IFile>();

		for (File file : files) {
			String fileName = file.getName();
			try {
				String packageName = getPackageFromFile(file);
				String ppaProjectName = getPPAProjectName(requestName);
				PPACoreJavaProjectHelper helper = new PPACoreJavaProjectHelper();
				IJavaProject javaProject = helper.setupJavaProject(ppaProjectName);
				IFile newFile = PPACoreResourceUtil.copyJavaSourceFile(javaProject.getProject(), file,
						packageName, fileName);
				iFiles.add(newFile);
			} catch (Exception e) {
				logger.error("Error while getting IFile from PPA", e);
			}
		}

		for (IFile file : iFiles) {
			logger.info("Getting CU for file: " + file.getLocation().toOSString());
			CompilationUnit cu = getCU(file, options);
			if (cu == null) {
				cu = getCUNoPPA(file);
			}
			cus.add(cu);
		}

		return cus;
	}

	/**
	 * <p>
	 * </p>
	 * 
	 * @param units
	 * @return
	 */
	public List<CompilationUnit> getCUs(List<ICompilationUnit> units) {

		if (units.size() == 0)
			return new ArrayList<CompilationUnit>();

		final List<CompilationUnit> astList = new ArrayList<CompilationUnit>();
		try {

			// FIXME a hack to get the current project.
			JavaProject jproject = (JavaProject) JavaCore.create(units.get(0)
					.getUnderlyingResource().getProject());
			PPATypeRegistry registry = new PPATypeRegistry(jproject);
			final PPAEngine ppaEngine = new PPAEngine(registry, new PPAOptions());

			PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
			parser2.setStatementsRecovery(true);
			parser2.setResolveBindings(true);
			parser2.setProject((IJavaProject) jproject);

			ASTRequestor requestor = new ASTRequestor() {

				@Override
				public void acceptAST(ICompilationUnit source, CompilationUnit ast) {
					astList.add(ast);
					ppaEngine.addUnitToProcess(ast);
				}
			};

			parser2.createASTs(units.toArray(new ICompilationUnit[units.size()]), new String[0],
					requestor, null);

			ppaEngine.doPPA();
			ppaEngine.reset();

		} catch (JavaModelException jme) {
			jme.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}

		return astList;
	}

	public static ASTNode getNode(IFile file, PPAOptions options, int kind) {
		ASTNode node = null;
		try {
			ICompilationUnit icu = JavaCore.createCompilationUnitFrom(file);
			PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
					.getUnderlyingResource().getProject()));
			PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
			parser2.setStatementsRecovery(true);
			parser2.setResolveBindings(true);
			parser2.setSource(icu);
			parser2.setKind(kind);
			node = parser2.createAST(true, null);
			PPAEngine ppaEngine = new PPAEngine(registry, options);

			ppaEngine.addUnitToProcess(node);
			ppaEngine.doPPA();
			ppaEngine.reset();
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}

		return node;
	}

	public static String getPackageFromFile(File file) throws IOException {
		String packageName = "";
		PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
		parser2.setStatementsRecovery(true);
		parser2.setResolveBindings(true);
		parser2.setSource(PPACoreResourceUtil.getContent(file).toCharArray());
		CompilationUnit cu = (CompilationUnit) parser2.createAST(true, null);
		PackageDeclaration pDec = cu.getPackage();
		if (pDec != null) {
			packageName = pDec.getName().getFullyQualifiedName();
		}
		return packageName;
	}

	public static String getPPAProjectName(String requestName) {
		PPACoreSingleton singleton = PPACoreSingleton.getInstance();
		String projectName = singleton.getProjectName();

		projectName += singleton.acquireId(requestName);

		return projectName;
	}

	public static ASTNode getSnippet(File file, PPAOptions options, boolean isTypeBody) {
		return getSnippet(file, options, isTypeBody, Thread.currentThread().getName());
	}

	public static ASTNode getSnippet(File file, PPAOptions options, boolean isTypeBody,
			String requestName) {
		CompilationUnit cu = null;
		try {
			String ppaProjectName = getPPAProjectName(requestName);
			PPACoreJavaProjectHelper helper = new PPACoreJavaProjectHelper();
			IJavaProject javaProject = helper.setupJavaProject(ppaProjectName);
			IFile newFile = PPACoreResourceUtil.copyJavaSourceFileSnippet(javaProject.getProject(),
					file, SnippetUtil.SNIPPET_PACKAGE, SnippetUtil.SNIPPET_FILE, isTypeBody);
			cu = getCU(newFile, options);
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}

		return cu;
	}

	public static ASTNode getSnippet(String codeSnippet, PPAOptions options, boolean isTypeBody) {
		return getSnippet(codeSnippet, options, isTypeBody, Thread.currentThread().getName());
	}

	public static ASTNode getSnippet(String codeSnippet, PPAOptions options, boolean isTypeBody,
			String requestName) {
		CompilationUnit cu = null;
		try {
			String ppaProjectName = getPPAProjectName(requestName);
			PPACoreJavaProjectHelper helper = new PPACoreJavaProjectHelper();
			IJavaProject javaProject = helper.setupJavaProject(ppaProjectName);
			IFile newFile = PPACoreResourceUtil.copyJavaSourceFileSnippet(javaProject.getProject(),
					codeSnippet, SnippetUtil.SNIPPET_PACKAGE, SnippetUtil.SNIPPET_FILE, isTypeBody);
			cu = getCU(newFile, options);
		} catch (Exception e) {
			logger.error("Error while getting CU from PPA", e);
		}

		return cu;
	}

}
