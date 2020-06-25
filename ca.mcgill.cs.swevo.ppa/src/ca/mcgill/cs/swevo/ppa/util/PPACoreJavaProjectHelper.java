/*******************************************************************************
 * PPA - Partial Program Analysis for Java
 * Copyright (C) 2010 Barthelemy Dagenais
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
package ca.mcgill.cs.swevo.ppa.util;

import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import org.apache.log4j.Logger;
import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;

@SuppressWarnings({ "restriction", "unchecked" })
public class PPACoreJavaProjectHelper {

	public static final String BIN = "bin";

	public static final String SRC = "src";

	private final Logger logger = Logger
			.getLogger(PPACoreJavaProjectHelper.class);

	private static final String FILENAME_CLASSPATH = ".classpath"; //$NON-NLS-1$

	private URI fCurrProjectLocation; // null if location is platform
	// location
	private IProject fCurrProject;

	private boolean fKeepContent;

	private Boolean fIsAutobuild;

	private IJavaProject fJavaProject;

	private String projectName;

	// This lock is only used so that one wizard page runs at a time.
	private final static Lock workbenchLock = new ReentrantLock(true);

	/**
	 * <p>
	 * Creates a Java project with an appropriate nature, classpath, and source
	 * folder in the workspace.
	 * </p>
	 * 
	 * @param projectName
	 * @return
	 * @throws Exception
	 */
	public IJavaProject setupJavaProject(String projectName) throws Exception {
		this.projectName = projectName;
		IJavaProject javaProject = null;

		IProject project = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(projectName);
		if (!project.exists()) {
			try {
				// workbenchLock.lock();
				createProject();
				javaProject = fJavaProject;
			} finally {
				// workbenchLock.unlock();
			}
		} else {
			javaProject = JavaCore.create(project);
		}

		javaProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);

		return javaProject;
	}

	// From now on, this code was inspired by JDT UI.
	public void createProject() throws CoreException, InterruptedException {
		try {
			if (fCurrProject == null) {
				updateProject();
			}
			configureJavaProject();

			if (!fKeepContent) {
				String compliance = JavaCore.VERSION_1_6;
				if (compliance != null) {
					IJavaProject project = JavaCore.create(fCurrProject);
					Map options = project.getOptions(false);
					JavaCore.setComplianceOptions(compliance, options);
					options.put(
							JavaCore.COMPILER_CODEGEN_INLINE_JSR_BYTECODE,
							!isVersionLessThan(compliance, JavaCore.VERSION_1_5) ? JavaCore.ENABLED
									: JavaCore.DISABLED);
					options.put(JavaCore.COMPILER_LOCAL_VARIABLE_ATTR,
							JavaCore.GENERATE);
					options.put(JavaCore.COMPILER_LINE_NUMBER_ATTR,
							JavaCore.GENERATE);
					options.put(JavaCore.COMPILER_SOURCE_FILE_ATTR,
							JavaCore.GENERATE);
					options.put(JavaCore.COMPILER_CODEGEN_UNUSED_LOCAL,
							JavaCore.PRESERVE);
					project.setOptions(options);
				}
			}
		} finally {
			fCurrProject = null;
			if (fIsAutobuild != null) {
				setAutoBuilding(fIsAutobuild.booleanValue());
				fIsAutobuild = null;
			}
		}
	}

	public static boolean setAutoBuilding(boolean state) throws CoreException {
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IWorkspaceDescription desc = workspace.getDescription();
		boolean isAutoBuilding = desc.isAutoBuilding();
		if (isAutoBuilding != state) {
			desc.setAutoBuilding(state);
			workspace.setDescription(desc);
		}
		return isAutoBuilding;
	}

	public static void createFolder(IFolder folder, boolean force,
			boolean local, IProgressMonitor monitor) throws CoreException {
		if (!folder.exists()) {
			IContainer parent = folder.getParent();
			if (parent instanceof IFolder) {
				createFolder((IFolder) parent, force, local, null);
			}
			folder.create(force, local, monitor);
		}
	}

	public static void createDerivedFolder(IFolder folder, boolean force,
			boolean local, IProgressMonitor monitor) throws CoreException {
		if (!folder.exists()) {
			IContainer parent = folder.getParent();
			if (parent instanceof IFolder) {
				createDerivedFolder((IFolder) parent, force, local, null);
			}
			folder.create(force ? (IResource.FORCE | IResource.DERIVED)
					: IResource.DERIVED, local, monitor);
		}
	}

	public static void addJavaNature(IProject project, IProgressMonitor monitor)
			throws CoreException {
		if (monitor != null && monitor.isCanceled()) {
			throw new OperationCanceledException();
		}
		if (!project.hasNature(JavaCore.NATURE_ID)) {
			IProjectDescription description = project.getDescription();
			String[] prevNatures = description.getNatureIds();
			String[] newNatures = new String[prevNatures.length + 1];
			System.arraycopy(prevNatures, 0, newNatures, 0, prevNatures.length);
			newNatures[prevNatures.length] = JavaCore.NATURE_ID;
			description.setNatureIds(newNatures);
			project.setDescription(description, monitor);
		} else {
			if (monitor != null) {
				monitor.worked(1);
			}
		}
	}

	public static void createProject(IProject project, URI locationURI,
			IProgressMonitor monitor) throws CoreException {
		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		monitor.beginTask("BuildPathsBlock_operationdesc_project", 10);

		// create the project
		try {
			if (!project.exists()) {
				IProjectDescription desc = project.getWorkspace()
						.newProjectDescription(project.getName());
				if (locationURI != null
						&& ResourcesPlugin.getWorkspace().getRoot()
								.getLocationURI().equals(locationURI)) {
					locationURI = null;
				}
				desc.setLocationURI(locationURI);
				project.create(desc, monitor);
				monitor = null;
			}
			if (!project.isOpen()) {
				project.open(monitor);
				monitor = null;
			}
		} finally {
			if (monitor != null) {
				monitor.done();
			}
		}
	}

	public static boolean isVersionLessThan(String version1, String version2) {
		if (JavaCore.VERSION_CLDC_1_1.equals(version1)) {
			version1 = JavaCore.VERSION_1_1 + 'a';
		}
		if (JavaCore.VERSION_CLDC_1_1.equals(version2)) {
			version2 = JavaCore.VERSION_1_1 + 'a';
		}
		return version1.compareTo(version2) < 0;
	}

	private final void updateProject() throws CoreException,
			InterruptedException {
		try {
			fCurrProject = ResourcesPlugin.getWorkspace().getRoot()
					.getProject(projectName);
			fCurrProjectLocation = null;

			URI realLocation = getRealLocation(projectName,
					fCurrProjectLocation);
			fKeepContent = hasExistingContent(realLocation);

			try {
				createProject(fCurrProject, fCurrProjectLocation);
			} catch (Exception e) {
			}

			initializeBuildPath(JavaCore.create(fCurrProject));
			configureJavaProject();
			try {
				List<IClasspathEntry> entries = getDefaultEntries();
				fJavaProject.setRawClasspath(
						entries.toArray(new IClasspathEntry[0]), true,
						new NullProgressMonitor());
			} catch (Exception e) {
				e.printStackTrace();
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private List<IClasspathEntry> getDefaultEntries() {
		List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();

		entries.add(JavaCore.newSourceEntry(new Path(Path.SEPARATOR + projectName
				+ Path.SEPARATOR + SRC)));
		entries.add(JavaCore.newContainerEntry(new Path(
				"org.eclipse.jdt.launching.JRE_CONTAINER")));
		return entries;
	}

	private boolean hasExistingContent(URI realLocation) throws CoreException {
		IFileStore file = EFS.getStore(realLocation);
		return file.fetchInfo().exists();
	}

	private IStatus changeToNewProject() {
		try {
			if (fIsAutobuild == null) {
				fIsAutobuild = Boolean.valueOf(setAutoBuilding(false));
			}
			updateProject();
		} catch (Exception e) {
			logger.error(e);
		}
		return Status.OK_STATUS;
	}

	private URI getRealLocation(String projectName, URI location) {
		if (location == null) {
			try {
				URI rootLocation = ResourcesPlugin.getWorkspace().getRoot()
						.getLocationURI();

				location = new URI(rootLocation.getScheme(), null, Path
						.fromPortableString(rootLocation.getPath())
						.append(projectName).toString(), null);
			} catch (URISyntaxException e) {
			}
		}
		return location;
	}

	protected void initializeBuildPath(IJavaProject javaProject)
			throws CoreException {

		try {
			IClasspathEntry[] entries = null;
			IPath outputLocation = null;
			IProject project = javaProject.getProject();

			List cpEntries = new ArrayList();
			IWorkspaceRoot root = project.getWorkspace().getRoot();

			IClasspathEntry[] sourceClasspathEntries = { JavaCore
					.newSourceEntry(new Path(Path.SEPARATOR + projectName + Path.SEPARATOR
							+ SRC)) };
			for (int i = 0; i < sourceClasspathEntries.length; i++) {
				IPath path = sourceClasspathEntries[i].getPath();
				if (path.segmentCount() > 1) {
					IFolder folder = root.getFolder(path);
					createFolder(folder, true, true, new NullProgressMonitor());
				}
				cpEntries.add(sourceClasspathEntries[i]);
			}

			cpEntries.add(getDefaultEntries().get(1));

			entries = (IClasspathEntry[]) cpEntries
					.toArray(new IClasspathEntry[cpEntries.size()]);

			outputLocation = new Path(Path.SEPARATOR + projectName + Path.SEPARATOR + BIN);
			if (outputLocation.segmentCount() > 1) {
				IFolder folder = root.getFolder(outputLocation);
				createDerivedFolder(folder, true, true,
						new NullProgressMonitor());
			}

			init(javaProject, outputLocation, entries, false);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	protected IProject createProvisonalProject() {
		changeToNewProject();
		return fCurrProject;
	}

	public void configureJavaProject() throws CoreException,
			InterruptedException {
		try {
			IProject project = fJavaProject.getProject();
			addJavaNature(project, new NullProgressMonitor());
		} catch (OperationCanceledException e) {
			throw new InterruptedException();
		}
	}

	public void createProject(IProject project, URI locationURI)
			throws CoreException {
		createProject(project, locationURI, new NullProgressMonitor());
	}

	public void init(IJavaProject jproject, IPath defaultOutputLocation,
			IClasspathEntry[] defaultEntries,
			boolean defaultsOverrideExistingClasspath) {
		if (!defaultsOverrideExistingClasspath && jproject.exists()
				&& jproject.getProject().getFile(".classpath").exists()) {
			defaultOutputLocation = null;
			defaultEntries = null;
		}
		fJavaProject = jproject;
	}

}
