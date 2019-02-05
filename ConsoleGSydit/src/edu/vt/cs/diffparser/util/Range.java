package edu.vt.cs.diffparser.util;

public class Range {

	int start;
	int end; //not included
	
	public Range(int start, int end) {
		this.start = start;
		this.end = end;
	}
	
//	public Range(String start, String end) {
//		this.start = Integer.getInteger(start);
//		this.end = Integer.getInteger(end);
//	}
	
	
	public int getStart() {
		return start;
	}



	public void setStart(int start) {
		this.start = start;
	}



	public int getEnd() {
		return end;
	}



	public void setEnd(int end) {
		this.end = end;
	}

	
	public boolean before(Range r) {
		return (end <= r.start);
	}
	
	public boolean after(Range r) {
		return start >= r.end;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + end;
		result = prime * result + start;
		return result;
	}
	
	public boolean isIncluded(Range r) {
		return r.start <= start && r.end >= end; 
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Range other = (Range) obj;
		if (end != other.end)
			return false;
		if (start != other.start)
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "Range" + "[" + start + ", " + end + "]"; 
	}
}
