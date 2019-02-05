package edu.vt.cs.prediction.neo;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.sql.SqliteManager;

/**
 * This class can be deleted at any time.
 * @author Ye Wang
 * @since  04/22/2018
 *
 */
public class Temp3 {
	
	public static void execute(String sourceTable, String targetTable) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + targetTable);
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + targetTable
				+ " (bug_name TEXT,af TEXT,cms TEXT,cm_num INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT count(*) FROM " + sourceTable);
		rs.next();
		int totalRow = rs.getInt(1);
		Gson gson = new Gson();
		java.lang.reflect.Type afToCmType = new TypeToken<Map<String, List<String>>>(){}.getType();
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + targetTable
				+ " (bug_name,af,cms,cm_num) VALUES (?,?,?,?)");
		for (int offset = 0; offset < totalRow; offset++) {
			rs = stmt.executeQuery("SELECT bug_name, af_cms FROM " + sourceTable + " LIMIT 1 OFFSET " + offset);
			rs.next();
			String bugName = rs.getString(1);
			String afCms = rs.getString(2);
			
			Map<String, List<String>> afToCm = gson.fromJson(afCms, afToCmType);
			
			for (String af: afToCm.keySet()) {
				ps.setString(1, bugName);
				ps.setString(2, af);
				List<String> cms = afToCm.get(af);
				String cmsJson = gson.toJson(cms);
				ps.setString(3, cmsJson);
				ps.setInt(4, cms.size());
				ps.executeUpdate();
				
			}
			
		}
		ps.close();
		stmt.close();
		conn.close();
		
	}

	public static void main(String[] args) throws SQLException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			String sourceTable = "af_commit_" + project;
			String targetTable = "af_commit_zz_" + project;
			execute(sourceTable, targetTable);
		}

	}

}
