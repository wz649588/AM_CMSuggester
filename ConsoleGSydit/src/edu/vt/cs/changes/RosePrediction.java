package edu.vt.cs.changes;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;

import edu.vt.cs.sql.SqliteManager;

/**
 * Tom Zimmerman's tool ROSE
 * @author Ye Wang
 * @since 04/13/2018
 */
public class RosePrediction {

	static final int minSupport = 1;
	
	static final double minConfidence = 0.1;
	
	private static final boolean DEBUG = true;
	
	public static String commitOrderTable;
	
	private static String merge(List<String> data) {
		if (data == null || data.isEmpty())
			return "";
		StringBuilder builder = new StringBuilder();
		for (int i = 0; i < data.size() - 1; i++) {
			builder.append("'").append(data.get(i)).append("'").append(",");
		}
		builder.append("'").append(data.get(data.size() - 1)).append("'");
		return builder.toString();
	}
	
	public static List<String> execute(List<String> evidenceMethods, String roseTable, String currentCommit) {
		Connection conn = SqliteManager.getConnection();
		Statement stmt;
		List<String> result = new ArrayList<>();
		try {
			stmt = conn.createStatement();
			
			ResultSet rset = stmt.executeQuery("SELECT ordering FROM " + commitOrderTable
					+ " WHERE bug_name='" + currentCommit + "'");
			if (!rset.next()) {
				stmt.close();
				conn.close();
				return result;
			}
			int currentOrder = rset.getInt(1);
			
			String orderQuery = "SELECT bug_name FROM " + commitOrderTable + " WHERE ordering<" + currentOrder;
			
			String miningQuery = "SELECT old_name, count(*) AS frequency "
					+ "FROM " + roseTable + " AS l, "
					+ "(SELECT bug_name FROM " + roseTable
						+ " WHERE old_name IN (" + merge(evidenceMethods) + ") "
						+ "AND bug_name IN (" + orderQuery + ")"
						+ " GROUP BY bug_name "
						+ "HAVING count(*)=" + evidenceMethods.size() + ") AS foo "
					+ "WHERE l.bug_name=foo.bug_name "
					+ "GROUP BY old_name "
					+ "HAVING count(*)>=" + minSupport;
			String resultQuery = "SELECT m.old_name, m.frequency FROM ("
					+ miningQuery + ") AS m "
					+ "ORDER BY m.frequency DESC";
			
			if (DEBUG)
				System.out.println(resultQuery);
			
			ResultSet rs = stmt.executeQuery(resultQuery);
			int maxSupport = -1;
			
			while (rs.next()) {
				String oldName = rs.getString(1);
				int support = rs.getInt(2);
				if (support > maxSupport)
					maxSupport = support; // This should be changed only once.
				if (!evidenceMethods.contains(oldName)) {
					double confidence = ((double) support) / maxSupport;
					if (DEBUG) {
						System.out.println("Support: " + support);
						System.out.println("MaxSupport: " + maxSupport);
						System.out.println("Confidence: " + confidence);
						System.out.println("------");
					}
					if (confidence > minConfidence) {
						result.add(oldName);
					}
				}
			}
			
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return result;
		
	}
}
