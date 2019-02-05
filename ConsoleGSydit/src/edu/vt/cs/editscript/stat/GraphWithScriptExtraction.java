package edu.vt.cs.editscript.stat;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * In the database table edit_script_mapping, many mappings do not have scripts. 
 * This class will find mappings with scripts and add them to a new table 
 * script_stat_mapping_with_script
 * @author Ye Wang
 * @since 04/13/2017
 */
public class GraphWithScriptExtraction {
	
	private static boolean executeFromScratch = true;
	
	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_mapping_with_script");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_mapping_with_script (bn1 TEXT, gn1 INTEGER, bn2 TEXT, gn2 INTEGER, mapping_num INTEGER, subgraph1 TEXT, subgraph2 TEXT, node_map TEXT, edge_map TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM edit_script_mapping");
		int totalMappingNum = rs.getInt(1);
		rs.close();
		
		for (int i = 0; i < totalMappingNum; i++) {
			System.out.println(i + " / " + totalMappingNum);
			String sql = "SELECT bn1, gn1, bn2, gn2, mapping_num, subgraph1, subgraph2, node_map, edge_map FROM edit_script_mapping LIMIT 1 OFFSET " + i;
			rs = stmt.executeQuery(sql);
			String bn1 = rs.getString(1);
			int gn1 = rs.getInt(2);
			String bn2 = rs.getString(3);
			int gn2 = rs.getInt(4);
			int mappingNum = rs.getInt(5);
			String subgraph1 = rs.getString(6);
			String subgraph2 = rs.getString(7);
			String nodeMap = rs.getString(8);
			String edgeMap = rs.getString(9);
			rs.close();
			
			Gson gson = new Gson();
			Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
			List<ScriptEdge> sg1 = gson.fromJson(subgraph1, scriptEdgeListType);
			List<ScriptEdge> sg2 = gson.fromJson(subgraph2, scriptEdgeListType);
			
			// check if graphs contains edit scripts
			boolean hasScript = graphContainsScript(sg1) && graphContainsScript(sg2);
			
			if (hasScript) {
				String sql2 = "INSERT INTO script_stat_mapping_with_script (bn1, gn1, bn2, gn2, mapping_num, subgraph1, subgraph2, node_map, edge_map) VALUES (?,?,?,?,?,?,?,?,?)";
				PreparedStatement pstmt = conn.prepareStatement(sql2);
				pstmt.setString(1, bn1);
				pstmt.setInt(2, gn1);
				pstmt.setString(3, bn2);
				pstmt.setInt(4, gn2);
				pstmt.setInt(5, mappingNum);
				pstmt.setString(6, subgraph1);
				pstmt.setString(7, subgraph2);
				pstmt.setString(8, nodeMap);
				pstmt.setString(9, edgeMap);
				pstmt.executeUpdate();
				pstmt.close();
			}
		}
		stmt.close();
		conn.close();
	}
	
	public static boolean graphContainsScript(List<ScriptEdge> edges) {
		for (ScriptEdge e: edges) {
			ScriptNode src = e.getSrc();
			if (nodeContainsScript(src))
				return true;
			
			ScriptNode dst = e.getDst();
			if (nodeContainsScript(dst))
				return true;
		}
		return false;
	}
	
	public static boolean nodeContainsScript(ScriptNode n) {
		if (n.getScript() == null)
			return false;
		if (n.getScript().isEmpty())
			return false;
		return true;
	}

}
