package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jgrapht.Graph;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

public class LargestMatchCollapser {

	// aries, cassandra, derby, mahout
	private String project = "mahout";
	
	private String patternTable = project + "_largest_match_pattern";
	
	private String collapsedPatternTable = project + "_largest_match_collapsed";
	
	private void setUpResultTable() {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			stmt.executeUpdate("DROP TABLE IF EXISTS " + collapsedPatternTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + collapsedPatternTable +
					" (pattern_id INTEGER, shape TEXT, collapsed_id TEXT, collapsed_shape TEXT)");
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private int currentEdgeType;
	private int currentTargetType;
	private int currentSourceType;
	
	/**
	 * Check if there is only one target in the graph, and the sources are the same type
	 * @return
	 */
	private boolean checkGraph(Graph<GraphNode, GraphEdge> graph) {
		if (graph.vertexSet().size() < 2)
			return false;
		
		int edgeType = -1;
		GraphNode target = null;
		for (GraphEdge e: graph.edgeSet()) {
			if (target == null) {
				edgeType = e.getType();
				target = e.getDst(); 
			} else if (e.getType() != edgeType || !e.getDst().equals(target)){
				return false;
			}
		}
		
		// no node
		if (target == null || edgeType == -1)
			return false;
		
		// the node points to itself
		if (graph.containsEdge(target, target))
			return false;
		
		// check types of source nodes
		int sourceType = -1;
		for (GraphEdge e: graph.edgeSet()) {
			if (sourceType == -1)
				sourceType = e.getSrc().getType();
			else if (sourceType != e.getSrc().getType())
				return false;
		}
		
		if (sourceType == -1)
			return false;
		
		currentEdgeType = edgeType;
		currentSourceType = sourceType;
		currentTargetType = target.getType();
		
		return true;
	}
	
	List<Map<String, Integer>> collapsedShapeList = new ArrayList<>();
	
	private int getCollapsedShapeIndex(Map<String, Integer> shape) {
		for (int i = 0; i < collapsedShapeList.size(); i++) {
			Map<String, Integer> s = collapsedShapeList.get(i);
			if (shape.get("edgeType").intValue() == s.get("edgeType").intValue()
					&& shape.get("sourceType").intValue() == s.get("sourceType").intValue()
					&& shape.get("targetType").intValue() == s.get("targetType").intValue()) {
				return i;
			}
		}
		return -1;
	}
	
	private String constructCollapsedShapeJson(Map<String, Integer> shape) {
//		Graph<GraphNode, GraphEdge>
		GraphDataJson json = new GraphDataJson();
		int sourceType = shape.get("sourceType");
		int targetType = shape.get("targetType");
		GraphNode source = json.new GraphNode("*" + ReferenceNode.getTypeString(sourceType), sourceType);
		GraphNode target = json.new GraphNode(ReferenceNode.getTypeString(targetType), targetType);
		GraphEdge edge = json.new GraphEdge(source, target, shape.get("edgeType").intValue(), -1);
		json.addEdge(edge);
		return json.toJson();
	}
	
	public void execute() {
		setUpResultTable();
		
		
		try {
			Connection conn = SqliteManager.getConnection();
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT count(*) FROM " + patternTable);
			rs.next();
			int totalNum = rs.getInt(1);
			
			PreparedStatement ps = conn.prepareStatement("INSERT INTO " + collapsedPatternTable +
					" (pattern_id, shape, collapsed_id, collapsed_shape) "
					+ "VALUES (?,?,?,?)");
			for (int offset = 0; offset < totalNum; offset++) {
				if (offset == 3)
					System.out.println("ha");
				rs = stmt.executeQuery("SELECT pattern_id, shape FROM " + patternTable + " LIMIT 1 OFFSET " + offset);
				rs.next();
				int patternId = rs.getInt(1);
				String shapeJson = rs.getString(2);
				rs.close();
				Graph<GraphNode, GraphEdge> graph = ExactMatchFinder.convertGraphJsonToObject(shapeJson);
				ps.setInt(1, patternId);
				ps.setString(2, shapeJson);
				if (checkGraph(graph)) {
					Map<String, Integer> collapsedShape = new HashMap<>();
					collapsedShape.put("edgeType", currentEdgeType);
					collapsedShape.put("sourceType", currentSourceType);
					collapsedShape.put("targetType", currentTargetType);
					int shapeIndex = this.getCollapsedShapeIndex(collapsedShape);
					if (shapeIndex == -1) {
						this.collapsedShapeList.add(collapsedShape);
						shapeIndex = collapsedShapeList.size() - 1;
					}
					
					
					
					ps.setString(3, "M" + shapeIndex);
					ps.setString(4, constructCollapsedShapeJson(collapsedShape));
					ps.executeUpdate();
					
				} else {
					ps.setString(3, Integer.toString(patternId));
					ps.setNull(4, java.sql.Types.VARCHAR);
					ps.executeUpdate();
				}
			}
			
			
			ps.close();
			
			
			
			// post processing
			rs = stmt.executeQuery("SELECT collapsed_id, COUNT(*) FROM "
					+ collapsedPatternTable + " WHERE collapsed_shape IS NOT NULL GROUP BY collapsed_id");
			List<String> onlyOneCollapsedIdList = new ArrayList<>();
			while (rs.next()) {
				String collapsedId = rs.getString(1);
				int idCount = rs.getInt(2);
				if (idCount == 1)
					onlyOneCollapsedIdList.add(collapsedId);
			}
			rs.close();
			for (String collapsedId: onlyOneCollapsedIdList) {
				List<Integer> patternIdList = new ArrayList<>();
				rs = stmt.executeQuery("SELECT pattern_id FROM " + collapsedPatternTable + " WHERE collapsed_id='" + collapsedId + "'");
				while (rs.next()) {
					int patternId = rs.getInt(1);
					patternIdList.add(patternId);
				}
				rs.close();
				for (int patternId: patternIdList) {
					stmt.executeUpdate("UPDATE " + collapsedPatternTable
							+ " SET collapsed_id='" + patternId
							+ "', collapsed_shape=NULL WHERE pattern_id=" + patternId);
				}
			}
			
			rs = stmt.executeQuery("SELECT collapsed_id FROM " + collapsedPatternTable);
			List<String> distinctCollapsedIdList = new ArrayList<>();
			while (rs.next()) {
				String collapsedId = rs.getString(1);
				if (collapsedId.startsWith("M") && !distinctCollapsedIdList.contains(collapsedId))
					distinctCollapsedIdList.add(collapsedId);
			}
			rs.close();
			for (int i = 0; i < distinctCollapsedIdList.size(); i++) {
				String newId = "C" + (i + 1);
				String sql = "UPDATE " + collapsedPatternTable
						+ " SET collapsed_id='" + newId
						+ "' WHERE collapsed_id='" + distinctCollapsedIdList.get(i) + "'";
				int rowCount = stmt.executeUpdate(sql);
				System.out.println(rowCount);
			}
			
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		
	}
	
	public static void main(String[] args) {
		LargestMatchCollapser collapser = new LargestMatchCollapser();
		collapser.execute();
	}
}
