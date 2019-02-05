package edu.vt.cs.editscript.json;

import java.util.List;

import edu.vt.cs.editscript.json.EditScriptJson.EditOperationJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;

public class ScriptNode {
	/**
	 * name of the method or the field
	 */
	private String name;
	
	/**
	 * Type of node, e.g. CM, AM, DM, AF, DF
	 */
	private int type;
	
	/**
	 * Edit script of the node
	 */
	private List<EditOperationJson> script;
	
	public ScriptNode(String name, int type) {
		this.name = name;
		this.type = type;
		this.script = null;
	}
	
	public ScriptNode(GraphNode n, EditScriptJson scriptMap) {
		name = n.getName();
		type = n.getType();
		
		if (type == ReferenceNode.CM || type == ReferenceNode.DM) {
			script = scriptMap.getOldScript(name);
		} else if (type == ReferenceNode.AM) {
			script = scriptMap.getNewScript(name);
		} else {
			script = null;
		}
	}
	
	public String getName() {
		return name;
	}
	
	public int getType() {
		return type;
	}
	
	public List<EditOperationJson> getScript() {
		return script;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (this.getClass() != obj.getClass())
			return false;
		ScriptNode n = (ScriptNode) obj;
		if (type != n.type)
			return false;
		if (name == null) {
			if (n.name != null)
				return false;
		} else if (!name.equals(n.name))
			return false;
		return true;
	}
	
	@Override
	public int hashCode() {
		return (name == null) ? 0 : name.hashCode();
	}

}
