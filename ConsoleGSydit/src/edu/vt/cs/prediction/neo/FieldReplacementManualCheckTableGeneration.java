package edu.vt.cs.prediction.neo;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

/**
 * Generate a database table for manually checking field replacement.
 * The database table is field_replacement_manual_check
 * @author Ye Wang
 *
 */
public class FieldReplacementManualCheckTableGeneration {

	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		stmt.executeUpdate("DROP TABLE IF EXISTS field_replacement_manual_check");
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS field_replacement_manual_check ("
				+ "bug_name TEXT, af_class TEXT, af_name TEXT, field_access TEXT, cm TEXT,"
				+ "verify TEXT,rp_type TEXT, old_entity TEXT, new_entity TEXT)");
		
		stmt.executeUpdate("INSERT INTO field_replacement_manual_check "
				+ "(bug_name,af_class,af_name,field_access,cm) "
				+ "SELECT bug_name,af_class,af_name,field_access,used_cm FROM prediction_cm_neo_derby");
		
		ResultSet rs = stmt.executeQuery("SELECT "
				+ "bug_name,af_class,af_name,cm,rp_type,old_entity,new_entity "
				+ "FROM field_replacement");
		
		PreparedStatement ps = conn.prepareStatement("UPDATE field_replacement_manual_check "
				+ "SET rp_type=?, old_entity=?, new_entity=? "
				+ "WHERE bug_name=? AND af_class=? AND af_name=? AND cm=?");
		while (rs.next()) {
			String bugName = rs.getString("bug_name");
			String afClass = rs.getString("af_class");
			String afName = rs.getString("af_name");
			String cm = rs.getString("cm");
			String rpType = rs.getString("rp_type");
			String oldEntity = rs.getString("old_entity");
			String newEntity = rs.getString("new_entity");
			ps.setString(1, rpType);
			ps.setString(2, oldEntity);
			ps.setString(3, newEntity);
			ps.setString(4, bugName);
			ps.setString(5, afClass);
			ps.setString(6, afName);
			ps.setString(7, cm);
			ps.executeUpdate();
		}
		ps.close();
		stmt.close();
		conn.close();
	}
}
