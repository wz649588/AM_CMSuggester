package edu.vt.cs.extraction;

import java.nio.file.Path;
import java.util.List;

/**
 * Supporting class for PatternExtractor
 * @author Ye Wang
 * @since 10/23/2016
 */
class BugGraphPaths {
	
	// Name of bug
	String name;
	
	// Paths of XML files storing JUNG DirectSparseGraph
	List<Path> xmlPaths;
	
	BugGraphPaths(String name, List<Path> xmlPaths) {
		this.name = name;
		this.xmlPaths = xmlPaths;
	}
}
