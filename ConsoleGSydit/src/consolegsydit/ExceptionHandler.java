package consolegsydit;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

/**
 * In Project ConsoleGSydit
 * Store the exception info into database, to facilitate further analysis of exception distribution.
 * @author Ye Wang
 * @since 02/20/2018
 *
 */
public class ExceptionHandler {
	private static boolean handlerIsEffective = false;
	
	private static String tableName = "exception_research";
	
	private static String currentCommitTable = "exception_research_current_commit";
	
	public static void initDatabaseTable(boolean clearPreviousData) throws SQLException {
		if (!handlerIsEffective)
			return;
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		if (clearPreviousData) {
			stmt.executeUpdate("DROP TABLE IF EXISTS " + tableName);
		}
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + tableName
				+ " (bug_name TEXT,type TEXT,message TEXT,stack TEXT,extra TEXT)");
		stmt.executeUpdate("DROP TABLE IF EXISTS " + currentCommitTable);
		stmt.executeUpdate("CREATE TABLE " + currentCommitTable + " (bug_name TEXT)");
		stmt.executeUpdate("INSERT INTO " + currentCommitTable + " (bug_name) VALUES (NULL)");
		stmt.close();
		conn.close();
	}
	
	public static void setCurrentCommit(String bugName) throws SQLException {
		if (!handlerIsEffective)
			return;
		Connection conn = SqliteManager.getConnection();
		PreparedStatement ps = conn.prepareStatement("UPDATE " + currentCommitTable + " SET bug_name=?");
		ps.setString(1, bugName);
		ps.executeUpdate();
		ps.close();
		conn.close();
	}
	
	public static void process(Throwable t) {
		process(t, "");
	}

	public static void process(Throwable t, String extraInfo) {
		if (!handlerIsEffective)
			return;
		String exceptionType = t.getClass().getName();
		String message = t.getMessage();
		StackTraceElement[] stackTraces = t.getStackTrace();
		StringBuilder builder = new StringBuilder();
		for (StackTraceElement e: stackTraces) {
			builder.append(e.toString());
			builder.append("\n");
		}
		String stackString = builder.toString();
		
		
		Connection conn = SqliteManager.getConnection();
		PreparedStatement ps;
		try {
			
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT bug_name FROM " + currentCommitTable);
			rs.next();
			String bugName = rs.getString(1);
			rs.close();
			stmt.close();
			
			ps = conn.prepareStatement("INSERT INTO " + tableName +
					" (bug_name,type,message,stack,extra) VALUES (?,?,?,?,?)");
			ps.setString(1, bugName);
			ps.setString(2, exceptionType);
			ps.setString(3, message);
			ps.setString(4, stackString);
			if (extraInfo == "") {
				ps.setNull(5, java.sql.Types.VARCHAR);
			} else {
				ps.setString(5, extraInfo);
			}
			ps.executeUpdate();
			
			ps.close();
		} catch (SQLException e1) {
			e1.printStackTrace();
		} finally {
			try {
				if (conn != null)
					conn.close();
			} catch (SQLException e1) {
				e1.printStackTrace();
			}
		}
		
		
	}
}
