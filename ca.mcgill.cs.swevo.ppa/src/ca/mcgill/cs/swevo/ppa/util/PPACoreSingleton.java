package ca.mcgill.cs.swevo.ppa.util;

import java.util.Queue;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.Semaphore;

public class PPACoreSingleton {
	
	private static PPACoreSingleton instance;
	
	private final Semaphore semaphore;

	private final Queue<Integer> threadIds;

	private final ConcurrentMap<String, Integer> threadIdMap = new ConcurrentHashMap<String, Integer>();

	private final String projectName;
	
	public final static String DEFAULT_PROJECT_NAME = "__PPA_PROJECT";
	
	public final static int DEFAULT_MAX_THREADS = 4;
	
	private PPACoreSingleton() {
		this(DEFAULT_MAX_THREADS, DEFAULT_PROJECT_NAME);
	}
	
	private PPACoreSingleton(int maxThreads, String projectName) {
		this.projectName = projectName;
		semaphore = new Semaphore(maxThreads, true);
		threadIds = new ArrayBlockingQueue<Integer>(maxThreads);
		for (int i = 0; i < maxThreads; i++) {
			threadIds.add(i);
		}
	}
	
	public static PPACoreSingleton getInstance(int maxThreads, String projectName) {
		if (instance == null) {
			instance = new PPACoreSingleton(maxThreads, projectName);
		}
		return instance;
	}
	
	public static PPACoreSingleton getInstance() {
		if (instance == null) {
			instance = new PPACoreSingleton();
		}
		
		return instance;
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
	
	public String getProjectName() {
		return projectName;
	}
}
