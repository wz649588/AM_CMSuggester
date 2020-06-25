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
package ca.mcgill.cs.swevo.ppa.ui;

import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import org.apache.log4j.Logger;
import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.corext.util.JavaModelUtil;
import org.eclipse.jdt.internal.ui.dialogs.StatusInfo;
import org.eclipse.jdt.internal.ui.util.CoreUtility;
import org.eclipse.jdt.internal.ui.wizards.ClassPathDetector;
import org.eclipse.jdt.internal.ui.wizards.buildpaths.BuildPathsBlock;
import org.eclipse.jdt.internal.ui.wizards.buildpaths.CPListElement;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.preference.IPreferenceStore;

@SuppressWarnings( { "restriction", "unchecked" })
public class PPAJavaProjectHelper {

	private final Logger logger = Logger.getLogger(PPAJavaProjectHelper.class);

	private static final String FILENAME_CLASSPATH = ".classpath"; //$NON-NLS-1$

	private NewJavaProjectWizardPageOne fFirstPage;

	private URI fCurrProjectLocation; // null if location is platform
	// location
	private IProject fCurrProject;

	private boolean fKeepContent;

	private Boolean fIsAutobuild;

	private IJavaProject fJavaProject;

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
		IJavaProject javaProject = null;

		IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(
				projectName);
		if (!project.exists()) {
			try {
//				workbenchLock.lock();
				fFirstPage = new NewJavaProjectWizardPageOne();
				fFirstPage.setProjectName(projectName);
				createProject();
				javaProject = fJavaProject;
			} finally {
//				workbenchLock.unlock();
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
				String compliance = fFirstPage.getCompilerCompliance();
				if (compliance != null) {
					IJavaProject project = JavaCore.create(fCurrProject);
					Map options = project.getOptions(false);
					JavaModelUtil.setComplianceOptions(options, compliance);
					JavaModelUtil.setDefaultClassfileOptions(options,
							compliance);
					project.setOptions(options);
				}
			}
		} finally {
			fCurrProject = null;
			if (fIsAutobuild != null) {
				CoreUtility.setAutoBuilding(fIsAutobuild.booleanValue());
				fIsAutobuild = null;
			}
		}
	}

	private final IStatus updateProject() throws CoreException,
			InterruptedException {
		IStatus result = StatusInfo.OK_STATUS;
		try {
			String projectName = fFirstPage.getProjectName();

			fCurrProject = ResourcesPlugin.getWorkspace().getRoot().getProject(
					projectName);
			fCurrProjectLocation = fFirstPage.getProjectLocationURI();

			URI realLocation = getRealLocation(projectName,
					fCurrProjectLocation);
			fKeepContent = hasExistingContent(realLocation);

			try {
				createProject(fCurrProject, fCurrProjectLocation);
			} catch (Exception e) {
			}

			initializeBuildPath(JavaCore.create(fCurrProject));
			configureJavaProject();
			List list = getDefaultClassPath(fJavaProject);
			try {
				List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();
				for (Object object : list) {
					CPListElement elem = (CPListElement) object;
					entries.add(elem.getClasspathEntry());
				}
				fJavaProject.setRawClasspath(entries
						.toArray(new IClasspathEntry[0]), true,
						new NullProgressMonitor());
			} catch (Exception e) {
				e.printStackTrace();
			}

		} catch (Exception e) {
		}
		return result;
	}

	private boolean hasExistingContent(URI realLocation) throws CoreException {
		IFileStore file = EFS.getStore(realLocation);
		return file.fetchInfo().exists();
	}

	private IStatus changeToNewProject() {
		try {
			if (fIsAutobuild == null) {
				fIsAutobuild = Boolean.valueOf(CoreUtility
						.setAutoBuilding(false));
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
						.fromPortableString(rootLocation.getPath()).append(
								projectName).toString(), null);
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

			if (fKeepContent) {
				if (!project.getFile(FILENAME_CLASSPATH).exists()) {
					final ClassPathDetector detector = new ClassPathDetector(
							fCurrProject, new NullProgressMonitor());
					entries = detector.getClasspath();
					outputLocation = detector.getOutputLocation();
					if (entries.length == 0) {
						entries = null;
					}
				}
			} else {
				List cpEntries = new ArrayList();
				IWorkspaceRoot root = project.getWorkspace().getRoot();

				IClasspathEntry[] sourceClasspathEntries = fFirstPage
						.getSourceClasspathEntries();
				for (int i = 0; i < sourceClasspathEntries.length; i++) {
					IPath path = sourceClasspathEntries[i].getPath();
					if (path.segmentCount() > 1) {
						IFolder folder = root.getFolder(path);
						CoreUtility.createFolder(folder, true, true,
								new NullProgressMonitor());
					}
					cpEntries.add(sourceClasspathEntries[i]);
				}

				cpEntries.addAll(Arrays.asList(fFirstPage
						.getDefaultClasspathEntries()));

				entries = (IClasspathEntry[]) cpEntries
						.toArray(new IClasspathEntry[cpEntries.size()]);

				outputLocation = fFirstPage.getOutputLocation();
				if (outputLocation.segmentCount() > 1) {
					IFolder folder = root.getFolder(outputLocation);
					CoreUtility.createDerivedFolder(folder, true, true,
							new NullProgressMonitor());
				}
			}

			init(javaProject, outputLocation, entries, false);
		} catch (Exception e) {
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
			BuildPathsBlock.addJavaNature(project, new NullProgressMonitor());
		} catch (OperationCanceledException e) {
			throw new InterruptedException();
		}
	}

	public void createProject(IProject project, URI locationURI)
			throws CoreException {
		BuildPathsBlock.createProject(project, locationURI,
				new NullProgressMonitor());
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

	private List getDefaultClassPath(IJavaProject jproj) {
		List list = new ArrayList();
		IResource srcFolder;
		IPreferenceStore store = PreferenceConstants.getPreferenceStore();
		String sourceFolderName = store
				.getString(PreferenceConstants.SRCBIN_SRCNAME);
		if (store.getBoolean(PreferenceConstants.SRCBIN_FOLDERS_IN_NEWPROJ)
				&& sourceFolderName.length() > 0) {
			srcFolder = jproj.getProject().getFolder(sourceFolderName);
		} else {
			srcFolder = jproj.getProject();
		}

		list.add(new CPListElement(jproj, IClasspathEntry.CPE_SOURCE, srcFolder
				.getFullPath(), srcFolder));

		IClasspathEntry[] jreEntries = PreferenceConstants
				.getDefaultJRELibrary();
		list.addAll(getExistingEntries(jreEntries));
		return list;
	}

	private ArrayList getExistingEntries(IClasspathEntry[] classpathEntries) {
		ArrayList newClassPath = new ArrayList();
		for (int i = 0; i < classpathEntries.length; i++) {
			IClasspathEntry curr = classpathEntries[i];
			newClassPath.add(CPListElement.createFromExisting(curr,
					fJavaProject));
		}
		return newClassPath;
	}

}
