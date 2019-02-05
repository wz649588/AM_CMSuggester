package edu.vt.cs.editscript.json;

import java.util.Objects;

public class ScriptEdge {
	/**
	 * Source vertex
	 */
	private ScriptNode src;
	
	/**
	 * Destination vertex
	 */
	private ScriptNode dst;
	
	/**
	 * Type of edge, e.g. method invocation, field access
	 */
	private int type;
	
	public ScriptEdge(ScriptNode src, ScriptNode dst, int type) {
		this.src = src;
		this.dst = dst;
		this.type = type;
	}
	
	public ScriptNode getSrc() {
		return src;
	}
	
	public ScriptNode getDst() {
		return dst;
	}
	
	public int getType() {
		return type;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (this.getClass() != obj.getClass())
			return false;
		ScriptEdge e = (ScriptEdge) obj;
		if (type != e.type)
			return false;
		if (src == null) {
			if (e.src != null)
				return false;
		} else if (!src.equals(e.src))
			return false;
		if (dst == null) {
			if (e.dst != null)
				return false;
		} else if (!dst.equals(e.dst))
			return false;
		return true;
	}
	
	@Override
	public int hashCode() {
		int result = 1;
		result = 37 * result + ((src == null) ? 0 : src.hashCode());
		result = 37 * result + ((dst == null) ? 0 : dst.hashCode());
		return src.hashCode();
	}
}
