package edu.vt.cs.editscript.stat;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

/**
 * ----------------------------------------
 * | Pattern ID | #(Commit) | #(Subgraph) |
 * ----------------------------------------
 * |      1     |     3     |      5      |
 * ----------------------------------------
 * Stored in table script_stat_pattern_group_num
 * 
 * @author Ye Wang
 * @since 04/19/2017
 *
 */
public class PatternGroupNumGeneration {
	
	private static boolean executeFromScratch = true;
	
	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_pattern_group_num");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_pattern_group_num (pattern_id INTEGER, commit_num INTEGER, subgraph_num INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT MAX(pattern_id) FROM script_stat_grouped_pattern");
		rs.next();
		int maxPatternId = rs.getInt(1);
		rs.close();
		
		rs = stmt.executeQuery("SELECT pattern_id, COUNT(DISTINCT(bug_name)), COUNT(*) FROM script_stat_pair_to_group GROUP BY pattern_id");
		PreparedStatement ps = conn.prepareStatement("INSERT INTO script_stat_pattern_group_num (pattern_id, commit_num, subgraph_num) VALUES (?,?,?)");
		while (rs.next()) {
			int pid = rs.getInt(1);
			int commitNum = rs.getInt(2);
			int subgraphNum = rs.getInt(3);
			ps.setInt(1, pid);
			ps.setInt(2, commitNum);
			ps.setInt(3, subgraphNum);
			ps.executeUpdate();
		}
		ps.close();
		stmt.close();
		conn.close();
	}
}
