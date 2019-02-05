package edu.vt.cs.editscript.common;

import java.util.Comparator;
import java.util.Iterator;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;

/**
 * Delete this class later, just for test
 * @author Ye Wang
 * @since 06/09/2017
 *
 */
public class Test1 {
	
	private static Comparator<Node> vertexComparator = new Comparator<Node>(){
		@Override
		public int compare(Node n1, Node n2) {
//			return n1.i - n2.i;
			return 0;
		}
	};
	
	private static Comparator<Edge> edgeComparator = new Comparator<Edge>(){
		@Override
		public int compare(Edge e1, Edge e2) {
			return 0;
		}
	};

	public static void main(String[] args) {
		Graph<Node, Edge> g1 = new DefaultDirectedGraph<>(Edge.class);
		Graph<Node, Edge> g2 = new DefaultDirectedGraph<>(Edge.class);
		
		Node n1 = new Node(1);
		Node n2 = new Node(2);
		Node n3 = new Node(3);
		Node n4 = new Node(4);
		
		g1.addVertex(n1);
		g1.addVertex(n2);
		g1.addVertex(n3);
		g1.addVertex(n4);
		g1.addEdge(n1, n2, new Edge());
		g1.addEdge(n1, n3, new Edge());
		g1.addEdge(n1, n4, new Edge());
		
		g2.addVertex(n1);
		g2.addVertex(n2);
		g2.addVertex(n3);
		g2.addEdge(n1, n2, new Edge());
		g2.addEdge(n1, n3, new Edge());
		
		VF2SubgraphIsomorphismInspector<Node,Edge> isoInspector =
				new VF2SubgraphIsomorphismInspector<>(g1, g2, vertexComparator, edgeComparator);
		
		int mappingNum = 0;
		Iterator<GraphMapping<Node, Edge>> isoIter = isoInspector.getMappings();
		while (isoIter.hasNext()) {
			mappingNum++;
			System.out.println("Mapping " + mappingNum);
			GraphMapping<Node, Edge> mapping = isoIter.next();
			for (Edge EdgeInG1: g1.edgeSet()) {
				Edge EdgeInG2 = mapping.getEdgeCorrespondence(EdgeInG1, true);
				if (EdgeInG2 != null) {
					Node SrcNodeG1 = g1.getEdgeSource(EdgeInG1);
					Node DstNodeG1 = g1.getEdgeTarget(EdgeInG1);
					System.out.println("G1: " + SrcNodeG1.i + " -> " + DstNodeG1.i);
					Node SrcNodeG2 = g2.getEdgeSource(EdgeInG2);
					Node DstNodeG2 = g2.getEdgeTarget(EdgeInG2);
					System.out.println("G2: " + SrcNodeG2.i + " -> " + DstNodeG2.i);
				}
			}
			System.out.println();
			
		}
		
		
	}
}

class Node {
	int i;
	Node(int i) { this.i = i; }
}

class Edge {
	
}