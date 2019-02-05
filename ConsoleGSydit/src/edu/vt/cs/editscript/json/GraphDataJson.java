package edu.vt.cs.editscript.json;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;
import com.ibm.wala.types.MemberReference;
import com.ibm.wala.types.TypeReference;

import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;

/**
 * This class is used to format the graph data into JSON
 * @author Ye Wang
 *
 */
public class GraphDataJson {
//	private Map<String, String> shortToFull;
//	private Map<String, String> fullToShort;
	
	protected List<GraphEdge> edges;
	
	public GraphDataJson() {
		edges = new ArrayList<GraphEdge>();
	}
	
	public List<GraphEdge> getEdges() {
		return edges;
	}
	
	public void addEdge(ReferenceEdge e) {
		GraphEdge newEdge = new GraphEdge(e);
		edges.add(newEdge);
	}
	
	public void addEdge(GraphEdge e) {
		edges.add(e);
	}
	
	public Graph<GraphNode, GraphEdge> getJgrapht() {
		Graph<GraphNode, GraphEdge> g = new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class);
		for (GraphEdge e: edges) {
			g.addVertex(e.src);
			g.addVertex(e.dst);
			g.addEdge(e.src, e.dst, e);
		}
		return g;
	}
	
	public static GraphDataJson convert(Graph<GraphNode, GraphEdge> g) {
		GraphDataJson json = new GraphDataJson();
		for (GraphEdge e: g.edgeSet()) {
			json.addEdge(e);
		}
		return json;
	}
	
	public String toJson() {
		Gson gson = new Gson();
		return gson.toJson(this);
	}
	
	public class GraphEdge {
		GraphNode src;
		GraphNode dst;
		int type;
		int dep;
		
		public GraphEdge(GraphNode src, GraphNode dst, int type, int dep) {
			this.src = src;
			this.dst = dst;
			this.type = type;
			this.dep = dep;
		}
		
		GraphEdge(ReferenceEdge e) {
			this.type = e.type;
			this.dep = e.dep;
			
			ReferenceNode srcRefNode = e.from;
			ReferenceNode dstRefNode = e.to;
			
//			src = new GraphNode(srcRefNode.ref.getSignature(), srcRefNode.type);
//			dst = new GraphNode(dstRefNode.ref.getSignature(), dstRefNode.type);
			src = new GraphNode(srcRefNode);
			dst = new GraphNode(dstRefNode);
		}
		
		/**
		 * Get the source node of this edge
		 * @return GraphNode
		 */
		public GraphNode getSrc() {
			return src;
		}
		
		/**
		 * Get the destination node of this edge
		 * @return GraphNode
		 */
		public GraphNode getDst() {
			return dst;
		}
		
		public int getType() {
			return type;
		}
		
		public int getDep() {
			return dep;
		}
		
		@Override
		public int hashCode() {
			int result = 5;
			result = 37 * result + (src == null ? 0 : src.hashCode());
			result = 37 * result + (dst == null ? 0 : dst.hashCode());
			result = 37 * result + type;
			return result;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (this.getClass() != obj.getClass())
				return false;
			GraphEdge e = (GraphEdge) obj;
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
		public String toString() {
			return src + "->" + dst;
		}
	}
	
	public class GraphNode {
		String name;
		int type;
		
		public GraphNode(String name, int type) {
			this.name = name;
			this.type = type;
		}
		
		public GraphNode(ReferenceNode node) {
			if (node.ref instanceof MemberReference)
				this.name = ((MemberReference) node.ref).getSignature();
			else { // node.ref instanceof TypeReference
				this.name = ((TypeReference) node.ref).getName().toString();
			}
			this.type = node.type;
		}
		
		public String getName() {
			return name;
		}
		
		public int getType() {
			return type;
		}
		
		@Override
		public int hashCode() {
			int result = 3;
			result = 37 * result + (name == null ? 0 : name.hashCode());
			result = 37 * result + type;
			return result;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (this.getClass() != obj.getClass())
				return false;
			GraphNode n = (GraphNode) obj;
			if (this.type != n.type)
				return false;
			if (!this.name.equals(n.name))
				return false;
			return true;
		}
		
		@Override
		public String toString() {
			return name;
		}
		
	}
	
}
