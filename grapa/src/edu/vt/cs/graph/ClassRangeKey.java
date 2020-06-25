package edu.vt.cs.graph;

public class ClassRangeKey {
	public String className;
	public int firstLine;
	public int lastLine;
	public ClassRangeKey(String name, int startLine, int endLine) {
		className = name;
		firstLine = startLine;
		lastLine = endLine;
	}
	
	public boolean containsLine(int line) {
		return firstLine <= line && lastLine >= line;
	}
	
	@Override
	public String toString() {
		return className + "(" + firstLine + ", " + lastLine + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((className == null) ? 0 : className.hashCode());
		result = prime * result + firstLine;
		result = prime * result + lastLine;
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ClassRangeKey other = (ClassRangeKey) obj;
		if (className == null) {
			if (other.className != null)
				return false;
		} else if (!className.equals(other.className))
			return false;
		if (firstLine != other.firstLine)
			return false;
		if (lastLine != other.lastLine)
			return false;
		return true;
	}
	
}
