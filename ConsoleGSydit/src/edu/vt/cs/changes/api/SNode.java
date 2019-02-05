package edu.vt.cs.changes.api;

public class SNode {

	protected String label;
	protected boolean mark = false;
	protected int type = 0;
	protected int id;
	
	public static final int DATA_NODE = 0;
	public static final int INST_NODE = 1;
	
	public SNode(String label, int t, int id) {
		this.label = label;
		this.type = t;
		this.id = id;
	}
	
	public void enableMark() {
		this.mark = true;
	}
	
	public String getContent() {
		return label;
	}
	
	public int getType() {
		return type;
	}
	
	@Override
	public String toString() {
		return label;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		SNode other = (SNode) obj;
		if (label == null) {
			if (other.label != null)
				return false;
		} else if (!label.equals(other.label))
			return false;
		if (id != other.id)
			return false;
		if (type != other.type)
			return false;
		return true;
	}

	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((label == null) ? 0 : label.hashCode());
		result = prime * result + id;
		result = prime * result + type;
		return result;
	}
}
