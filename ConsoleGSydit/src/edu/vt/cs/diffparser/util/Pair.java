package edu.vt.cs.diffparser.util;

public class Pair<T1, T2> {
	protected T1 left;
	protected T2 right;
	public Pair(T1 l, T2 r) {
		left = l;
		right = r;
	}
	
	public T1 getLeft() {
		return left;
	}
	
	public T2 getRight() {
		return right;
	}
	
	public void setRight(T2 val) {
		right = val;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
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
		Pair other = (Pair) obj;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (right == null) {
			if (other.right != null)
				return false;
		} else if (!right.equals(other.right))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "[" + left + ", " + right + "],";  
	}
}
