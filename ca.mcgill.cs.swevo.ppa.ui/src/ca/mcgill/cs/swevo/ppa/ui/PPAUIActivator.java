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

import java.util.Queue;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.Semaphore;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

public class PPAUIActivator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "ca.mcgill.cs.swevo.ppa.ui";

	// The shared instance
	private static PPAUIActivator plugin;

	private Logger logger;

	private Semaphore semaphore;

	private Queue<Integer> threadIds;

	private ConcurrentMap<String, Integer> threadIdMap = new ConcurrentHashMap<String, Integer>();

	private int maxThreads;

	/**
	 * Returns the shared instance
	 * 
	 * @return the shared instance
	 */
	public static PPAUIActivator getDefault() {
		return plugin;
	}

	public PPAUIActivator() {
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
	 * )
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		maxThreads = getPreferenceStore().getInt(
				PPAPreferenceConstants.PPA_MAX_REQUESTS);
//		maxThreads = 10;
		semaphore = new Semaphore(maxThreads, true);
		threadIds = new ArrayBlockingQueue<Integer>(maxThreads);
		for (int i = 0; i < maxThreads; i++) {
			threadIds.add(i);
		}

		PropertyConfigurator.configure(this.getBundle().getEntry(
				"log4j.properties"));
		logger = Logger.getLogger(PPAUIActivator.class);
		logger.info("PPA UI Started");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
	 * )
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		logger.info("PPA UI Stopped");
		super.stop(context);
	}

	/**
	 * <p>
	 * Generates a project id to append to the PPA project name. A unique
	 * project id is assigned to each different request for any given concurrent
	 * requests. The id can then be reused by another request once the current
	 * request has released it.
	 * </p>
	 * 
	 * @param requestName
	 *            The name of the request
	 * @return
	 */
	public int acquireId(String requestName) {
		int id = -1;
		if (threadIdMap.containsKey(requestName)) {
			id = threadIdMap.get(requestName);
		} else {
			try {
				semaphore.acquire();
				id = threadIds.remove();
				threadIdMap.put(requestName, id);
			} catch (Exception e) {
				throw new RuntimeException(e);
			}
		}
		return id;
	}

	/**
	 * <p>
	 * Releases the id associated with this request.
	 * </p>
	 * 
	 * @param requestName
	 *            The name of the request
	 */
	public void releaseId(String requestName) {
		if (threadIdMap.containsKey(requestName)) {
			int id = threadIdMap.remove(requestName);
			threadIds.add(id);
			semaphore.release();
		}
	}

	public Semaphore getSemaphore() {
		return semaphore;
	}

}
