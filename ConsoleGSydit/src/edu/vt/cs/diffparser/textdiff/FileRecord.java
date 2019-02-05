package edu.vt.cs.diffparser.textdiff;

import java.util.ArrayList;
import java.util.List;

import edu.vt.cs.diffparser.util.Pair;
import edu.vt.cs.diffparser.util.Range;

public class FileRecord {

	protected String fileName;
	protected List<Pair<Range, Range>> rangePairs;
	
	public FileRecord(String f) {
		this.fileName = f;
		rangePairs = new ArrayList<Pair<Range, Range>>();
	}
	
	public String getName() {
		return fileName;
	}
	
	public List<Pair<Range, Range>> getRangePairs() {
		return rangePairs;
	}
	
	public void addRangePair(Range r1, Range r2) {
		rangePairs.add(new Pair<Range, Range>(r1, r2));
	}
	
	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder(fileName);
		for(Pair<Range, Range> p : rangePairs) {
			builder.append("\n").append(p);
		}
		return builder.toString();
	}
}
