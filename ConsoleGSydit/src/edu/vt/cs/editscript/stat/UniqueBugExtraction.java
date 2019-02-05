package edu.vt.cs.editscript.stat;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

/**
 * In the intersection of unique_bug table and edit_script_table,
 * there are still some duplicate bugs. We will eliminate them
 * 
 * @author Ye Wang
 * @since 04/17/2017
 *
 */
public class UniqueBugExtraction {
	
	public static void main(String[] args) throws SQLException {
		String[] bugsToBeRemoved = {"902857_DERBY-4477", "644764_DERBY-3354"};
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		PreparedStatement ps = conn.prepareStatement("DELETE FROM unique_bug WHERE bug_name=?");
		for (String bug: bugsToBeRemoved) {
			ps.setString(1, bug);
			ps.executeUpdate();
		}
		ps.close();
		conn.close();
		
	}

}
