package edu.vt.cs.extraction;

import java.util.Iterator;

import org.jgrapht.EdgeFactory;
import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;


public class Temp {

	public static void main(String[] args) {
		EdgeBuilder edgeBuilder = new EdgeBuilder();
		
		Graph<Vertex, Edge> graphA =
				new DefaultDirectedGraph<Vertex, Edge>(edgeBuilder);
		Vertex a0 = new Vertex("a0");
		Vertex a1 = new Vertex("a1");
		Vertex a2 = new Vertex("a2");
		graphA.addVertex(a0);
		graphA.addVertex(a1);
		graphA.addVertex(a2);
		graphA.addEdge(a0, a1);
		graphA.addEdge(a0, a2);
		
		Graph<Vertex, Edge> graphB =
				new DefaultDirectedGraph<Vertex, Edge>(edgeBuilder);
		Vertex b0 = new Vertex("b0");
		Vertex b1 = new Vertex("b1");
		Vertex b2 = new Vertex("b2");
		graphB.addVertex(b0);
		graphB.addVertex(b1);
		graphB.addVertex(b2);
		graphB.addEdge(b0, b1);
		graphB.addEdge(b0, b2);
		
		VF2SubgraphIsomorphismInspector<Vertex, Edge> isoInspector =
				new VF2SubgraphIsomorphismInspector<Vertex, Edge>(graphA, graphB);
		Iterator<GraphMapping<Vertex, Edge>> isoIterator = isoInspector.getMappings();
		
		int mappingNum = 0;
		while (isoIterator.hasNext()) {
			mappingNum++;
			
			Graph<Vertex, Edge> subg1 = new DefaultDirectedGraph<Vertex, Edge>(edgeBuilder);
			Graph<Vertex, Edge> subg2 = new DefaultDirectedGraph<Vertex, Edge>(edgeBuilder);
			
			GraphMapping<Vertex, Edge> mapping = isoIterator.next();
			
			for (Vertex va: graphA.vertexSet()) {
				Vertex vb = mapping.getVertexCorrespondence(va, true);
				if (vb != null) {
					subg1.addVertex(va);
					subg2.addVertex(vb);
				}
			}
			
			for (Edge ea: graphA.edgeSet()) {
				Edge eb = mapping.getEdgeCorrespondence(ea, true);
				if (eb != null) {
					subg1.addEdge(ea.from, ea.to, ea);
					subg2.addEdge(eb.from, eb.to, eb);
				}
			}
			
			System.out.println("mapping " + mappingNum + ":");
			System.out.println(subg1);
			System.out.println(subg2);
			
		}
	}

}

class Vertex {
	String name;
	Vertex(String name) {
		this.name = name;
	}
	
	@Override
	public String toString() {
		return name;
	}
}

class Edge {
	Vertex from;
	Vertex to;
	
	Edge(Vertex from, Vertex to) {
		this.from = from;
		this.to = to;
	}
	
//	@Override
//	public String toString() {
//		return from.toString() + "->" + to.toString();
//	}
}

class EdgeBuilder implements EdgeFactory<Vertex, Edge> {

	@Override
	public Edge createEdge(Vertex from, Vertex to) {
		return new Edge(from, to);
	}
	
}
