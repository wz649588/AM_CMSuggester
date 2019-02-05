package edu.vt.cs.editscript.stat;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2GraphIsomorphismInspector;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * Some isomorphism pairs may share the same shape. They should be grouped into
 * the same category. The grouped pattern will be stored in the database table
 * script_stat_grouped_pattern, and the original data with the pattern number will
 * be stored in script_stat_data_with_pattern. 
 * 
 * @author Ye Wang
 * @since 04/15/2017
 *
 */
public class IsoPairGrouper {
	
	private static boolean executeFromScratch = true;
	
	private static Connection conn = null;
	
	private static Connection getConnection() {
		if (conn == null)
			conn = SqliteManager.getConnection();
		return conn;
	}
	
	public static void main(String[] args) throws SQLException {
		
		Connection conn = getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch) {
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_grouped_pattern");
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_data_with_pattern");
		}
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_grouped_pattern (pattern_id INTEGER PRIMARY KEY, shape TEXT)");
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_data_with_pattern (bn1 TEXT, gn1 INTEGER, bn2 TEXT, gn2 INTEGER, mapping_num INTEGER, subgraph1 TEXT, subgraph2 TEXT, node_map TEXT, edge_map TEXT, pattern_id INTEGER, pattern_node_map TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM script_stat_refined_mapping");
		rs.next();
		int totalMappingNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		Gson gson2 = new GsonBuilder().enableComplexMapKeySerialization().create();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO script_stat_data_with_pattern (bn1,gn1,bn2,gn2,mapping_num,subgraph1,subgraph2,node_map,edge_map,pattern_id,pattern_node_map) VALUES (?,?,?,?,?,?,?,?,?,?,?)");
		
		for (int offset = 0; offset < totalMappingNum; offset++) {
			rs = stmt.executeQuery("SELECT bn1, gn1, bn2, gn2, mapping_num, subgraph1, subgraph2, node_map, edge_map FROM script_stat_refined_mapping LIMIT 1 OFFSET " + offset);
			rs.next();
			String bn1 = rs.getString(1);
			int gn1 = rs.getInt(2);
			String bn2 = rs.getString(3);
			int gn2 = rs.getInt(4);
			int mappingNum = rs.getInt(5);
			String subgraph1 = rs.getString(6);
			String subgraph2 = rs.getString(7);
			String nodeMap = rs.getString(8);
			String edgeMap = rs.getString(9);
			
			List<ScriptEdge> edges = gson.fromJson(subgraph1, scriptEdgeListType);
			
			// check if the shape already exists in script_stat_grouped_pattern
			Graph<ScriptNode, ScriptEdge> graph = RedundancyElimination.buildGraph(edges);
//			Integer returnedShapeId = getShapeId(graph);
			
			// Get shape ID
			rs = stmt.executeQuery("SELECT COUNT(*) FROM script_stat_grouped_pattern");
			rs.next();
			int totalShapeNum = rs.getInt(1);
			rs.close();
			
			Map<ScriptNode, ScriptNode> shapeNodeMapping = new HashMap<>(); // Shape Node -> Graph Node
			Integer shapeId = null;
			Graph<ScriptNode, ScriptEdge> shape = null;
			for (int shapeOffset = 0; shapeOffset < totalShapeNum; shapeOffset++) {
				rs = stmt.executeQuery("SELECT pattern_id, shape FROM script_stat_grouped_pattern LIMIT 1 OFFSET " + shapeOffset);
				rs.next();
				int patternId = rs.getInt(1);
				String shapeJson = rs.getString(2);
				List<ScriptEdge> shapeEdges = gson.fromJson(shapeJson, scriptEdgeListType);
				shape = RedundancyElimination.buildGraph(shapeEdges);
				VF2GraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
						new VF2GraphIsomorphismInspector<>(shape, graph,
								RedundancyElimination.nodeComparator, RedundancyElimination.edgeComparator);
				if (isoInspector.isomorphismExists()) {
					shapeId = patternId;
					
					// Get node mapping
					Iterator<GraphMapping<ScriptNode, ScriptEdge>> mappingIter = isoInspector.getMappings();
					GraphMapping<ScriptNode, ScriptEdge> mapping = mappingIter.next();
					for (ScriptNode n: shape.vertexSet()) {
						shapeNodeMapping.put(n, mapping.getVertexCorrespondence(n, true));
					}
					
					break;
				}
			}
			
			
//			int shapeId;
			if (shapeId == null) {
//				List<ScriptEdge> newShape = generateNewShape(edges);
				
				List<ScriptEdge> newShape = new ArrayList<>();
				Map<ScriptNode, Integer> nodeIndices = new HashMap<>();
				
				int currentIndex = 0;
				for (ScriptEdge e: edges) {
					ScriptNode src = e.getSrc();
					ScriptNode dst = e.getDst();
					int srcIndex;
					int dstIndex;
					if (nodeIndices.containsKey(src))
						srcIndex = nodeIndices.get(src);
					else {
						nodeIndices.put(src, currentIndex);
						srcIndex = currentIndex;
						currentIndex++;
					}
					if (nodeIndices.containsKey(dst))
						dstIndex = nodeIndices.get(dst);
					else {
						nodeIndices.put(dst, currentIndex);
						dstIndex = currentIndex;
						currentIndex++;
					}
					String srcName = ReferenceNode.getTypeString(src.getType()) + srcIndex;
					ScriptNode srcNode = new ScriptNode(srcName, src.getType());
					String dstName = ReferenceNode.getTypeString(dst.getType()) + dstIndex;
					ScriptNode dstNode = new ScriptNode(dstName, dst.getType());
					ScriptEdge newEdge = new ScriptEdge(srcNode, dstNode, e.getType());
					newShape.add(newEdge);
					
					if (!shapeNodeMapping.containsKey(srcNode))
						shapeNodeMapping.put(srcNode, src);
					if (!shapeNodeMapping.containsKey(dstNode))
						shapeNodeMapping.put(dstNode, dst);
				}
				
				shape = RedundancyElimination.buildGraph(newShape);
				
				shapeId = insertNewShape(newShape);
			}
			
			// Build Pattern Node Map
			Map<String, ScriptNode> patternNodeMap = new HashMap<>();
			for (ScriptNode n: shape.vertexSet()) {
				patternNodeMap.put(n.getName(), shapeNodeMapping.get(n));
			}
			
			ps.setString(1, bn1);
			ps.setInt(2, gn1);
			ps.setString(3, bn2);
			ps.setInt(4, gn2);
			ps.setInt(5, mappingNum);
			ps.setString(6, subgraph1);
			ps.setString(7, subgraph2);
			ps.setString(8, nodeMap);
			ps.setString(9, edgeMap);
			ps.setInt(10, shapeId);
			ps.setString(11, gson2.toJson(patternNodeMap));
			ps.executeUpdate();
			
		}
		
		ps.close();
		
		stmt.close();
		conn.close();
	}
	
	private static List<ScriptEdge> generateNewShape(List<ScriptEdge> edges) {
		// build a new graph for storage
		List<ScriptEdge> newShape = new ArrayList<>();
		Map<ScriptNode, Integer> nodeIndices = new HashMap<>();
		int currentIndex = 0;
		for (ScriptEdge e: edges) {
			ScriptNode src = e.getSrc();
			ScriptNode dst = e.getDst();
			int srcIndex;
			int dstIndex;
			if (nodeIndices.containsKey(src))
				srcIndex = nodeIndices.get(src);
			else {
				nodeIndices.put(src, currentIndex);
				srcIndex = currentIndex;
				currentIndex++;
			}
			if (nodeIndices.containsKey(dst))
				dstIndex = nodeIndices.get(dst);
			else {
				nodeIndices.put(dst, currentIndex);
				dstIndex = currentIndex;
				currentIndex++;
			}
			String srcName = ReferenceNode.getTypeString(src.getType()) + srcIndex;
			ScriptNode srcNode = new ScriptNode(srcName, src.getType());
			String dstName = ReferenceNode.getTypeString(dst.getType()) + dstIndex;
			ScriptNode dstNode = new ScriptNode(dstName, dst.getType());
			ScriptEdge newEdge = new ScriptEdge(srcNode, dstNode, e.getType());
			newShape.add(newEdge);
		}
		return newShape;
	}
	
	private static int insertNewShape(List<ScriptEdge> edges) throws SQLException {
		Connection conn = getConnection();
		
		Gson gson = new Gson();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		
		String shapeJson = gson.toJson(edges, scriptEdgeListType);
		PreparedStatement ps = conn.prepareStatement("INSERT INTO script_stat_grouped_pattern (shape) VALUES (?)", Statement.RETURN_GENERATED_KEYS);
		ps.setString(1, shapeJson);
		ps.executeUpdate();
		ResultSet rs = ps.getGeneratedKeys();
		rs.next();
		int shapeId = rs.getInt(1);
		
		ps.close();
//		conn.close();
		
		return shapeId;
	}

	/**
	 * Check if the graph shape exists in table script_stat_grouped_pattern.
	 * If exists, return shape ID.
	 * @param graph
	 * @return shape ID if shape exists, otherwise null
	 * @throws SQLException 
	 */
	private static Integer getShapeId(Graph<ScriptNode, ScriptEdge> graph) throws SQLException {
		Connection conn = getConnection();
		Statement stmt = conn.createStatement();
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM script_stat_grouped_pattern");
		rs.next();
		int totalShapeNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		
		Integer shapeId = null;
		for (int offset = 0; offset < totalShapeNum; offset++) {
			rs = stmt.executeQuery("SELECT pattern_id, shape FROM script_stat_grouped_pattern LIMIT 1 OFFSET " + offset);
			rs.next();
			int patternId = rs.getInt(1);
			String shapeJson = rs.getString(2);
			List<ScriptEdge> shapeEdges = gson.fromJson(shapeJson, scriptEdgeListType);
			Graph<ScriptNode, ScriptEdge> shape = RedundancyElimination.buildGraph(shapeEdges);
			VF2GraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
					new VF2GraphIsomorphismInspector<>(shape, graph,
							RedundancyElimination.nodeComparator, RedundancyElimination.edgeComparator);
			if (isoInspector.isomorphismExists()) {
				shapeId = patternId;
				break;
			}
		}
		
		stmt.close();
//		conn.close();
		
		return shapeId;
	}

}
