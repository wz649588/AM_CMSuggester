package edu.vt.cs.changes.api;

import org.eclipse.jdt.core.dom.CompilationUnit;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class LineRange {

	public int startLine;
	public int endLine;
	
	public LineRange(int startLine, int endLine) {
		this.startLine = startLine;
		this.endLine = endLine;
	}
	
	public static LineRange get(CompilationUnit cu, SourceCodeRange r) {
		return new LineRange(cu.getLineNumber(r.startPosition), cu.getLineNumber(r.startPosition + r.length - 1));
	}
	
}
