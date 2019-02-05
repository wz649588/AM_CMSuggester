package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.HashMap;
import java.util.Map;
import java.lang.reflect.Field;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;

import org.jgrapht.EdgeFactory;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.EdgeSetFactory;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.InstanceCreator;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.sql.SqliteManager;

public class IsomorphismValidation {
	
	public static class GraphInstanceCreator implements InstanceCreator<DefaultDirectedGraph<GraphNode, GraphEdge>> {
		
		@Override
		public DefaultDirectedGraph<GraphNode, GraphEdge> createInstance(
				Type arg0) {
			return new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class);
		}
		
	}
	
	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS temp_iso_check (mapping1 INTEGER, mapping2 INTEGER)");
		ResultSet rs = stmt.executeQuery("SELECT MAX(mapping_num) FROM temp_isomorphism");
		int maxMapping = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
//		DefaultDirectedGraph<GraphNode, GraphEdge> graphObject = new DefaultDirectedGraph<>(GraphEdge.class);
		Type graphType = new TypeToken<DefaultDirectedGraph<GraphNode, GraphEdge>>() {}.getType();
		Type nodeMapType = new TypeToken<HashMap<GraphNode, GraphNode>>() {}.getType();
		Type edgeMapType = new TypeToken<HashMap<GraphEdge, GraphEdge>>() {}.getType();
		
		GsonBuilder gsonBuilder = new GsonBuilder();
//		InstanceCreator<DefaultDirectedGraph<GraphNode, GraphEdge>> instanceCreator =
//				new InstanceCreator<DefaultDirectedGraph<GraphNode, GraphEdge>> {};
		gsonBuilder.registerTypeAdapter(new TypeToken<DefaultDirectedGraph<GraphNode, GraphEdge>>() {}.getType(), 
				new GraphInstanceCreator());
		
		gsonBuilder.registerTypeAdapter(new TypeToken<EdgeFactory<GraphNode, GraphEdge>>() {}.getType(),
				new InstanceCreator<EdgeFactory<GraphNode, GraphEdge>>() {
					@Override
					public EdgeFactory<GraphNode, GraphEdge> createInstance(Type arg0) {
						return new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class).getEdgeFactory();
					}});
		
		gsonBuilder.registerTypeAdapter(new TypeToken<EdgeSetFactory<GraphNode, GraphEdge>>() {}.getType(),
				new InstanceCreator<EdgeSetFactory<GraphNode, GraphEdge>>() {
					@Override
					public EdgeSetFactory<GraphNode, GraphEdge> createInstance(
							Type arg0) {
						DefaultDirectedGraph<GraphNode, GraphEdge> graph =
								new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class);
						Class<?> klass0 = graph.getClass();
						ParameterizedType klass1 = (ParameterizedType) klass0.getGenericSuperclass();
						Class<?> klass = (Class<?>) klass1.getRawType();
//						klass0.get
						Field field = null;
						try {
							field = klass.getDeclaredField("edgeSetFactory");
						} catch (NoSuchFieldException | SecurityException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						field.setAccessible(true);
						Object fieldObject = null;
						try {
							fieldObject = field.get(graph);
						} catch (IllegalArgumentException
								| IllegalAccessException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						return (EdgeSetFactory<GraphNode, GraphEdge>) fieldObject;
					}});
		
		Gson graphGson = gsonBuilder.create();
		
		
		for (int i = 0; i < maxMapping; i++) {
			
			System.out.println("i=" + i);
			
			rs = stmt.executeQuery("SELECT sg1, sg2, node_map, edge_map FROM temp_isomorphism WHERE mapping_num=" + i);
			String leftSg1Json = rs.getString(1);
			String leftSg2Json = rs.getString(2);
			String leftNodeMapJson = rs.getString(3);
			String leftEdgeMapJson = rs.getString(4);
			rs.close();
			
			Graph<GraphNode, GraphEdge> leftSg1 = gson.fromJson(leftSg1Json, GraphDataJson.class).getJgrapht();
			Graph<GraphNode, GraphEdge> leftSg2 = gson.fromJson(leftSg2Json, GraphDataJson.class).getJgrapht();
			HashMap<GraphNode, GraphNode> leftNodeMap = gson.fromJson(leftNodeMapJson, nodeMapType);
			HashMap<GraphEdge, GraphEdge> leftEdgeMap = gson.fromJson(leftEdgeMapJson, edgeMapType);
			
			
			for (int j = i + 1; j <= maxMapping; j++) {
				
//				System.out.println("j=" + j);
				
				rs = stmt.executeQuery("SELECT sg1, sg2, node_map, edge_map FROM temp_isomorphism WHERE mapping_num=" + j);
				String rightSg1Json = rs.getString(1);
				String rightSg2Json = rs.getString(2);
				String rightNodeMapJson = rs.getString(3);
				String rightEdgeMapJson = rs.getString(4);
				rs.close();
				
				Graph<GraphNode, GraphEdge> rightSg1 = gson.fromJson(rightSg1Json, GraphDataJson.class).getJgrapht();
				Graph<GraphNode, GraphEdge> rightSg2 = gson.fromJson(rightSg2Json, GraphDataJson.class).getJgrapht();
				HashMap<GraphNode, GraphNode> rightNodeMap = gson.fromJson(rightNodeMapJson, nodeMapType);
				HashMap<GraphEdge, GraphEdge> rightEdgeMap = gson.fromJson(rightEdgeMapJson, edgeMapType);
				
				if (leftSg1.equals(rightSg1) &&
						leftSg2.equals(rightSg2) &&
						leftNodeMap.equals(rightNodeMap) &&
						leftEdgeMap.equals(rightEdgeMap)) {
					System.err.println("EQUALS: i=" + i + ", j=" + j);
					stmt.executeUpdate("INSERT INTO temp_iso_check (mapping1, mapping2) VALUES ("+i+","+j+")");
				}
				
			}
			
		}
		stmt.close();
		conn.close();
	}
	
}
