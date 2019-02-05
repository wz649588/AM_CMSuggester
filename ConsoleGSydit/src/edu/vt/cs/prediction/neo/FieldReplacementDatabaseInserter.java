package edu.vt.cs.prediction.neo;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class FieldReplacementDatabaseInserter {
	
	private String bugName;
	private String afClass;
	private String afName;
	private String fieldAccess;
	private String cmSig;
	private String fieldReplacementTable;

	public FieldReplacementDatabaseInserter(String bugName, String afClass,
			String afName, String fieldAccess, String cmSig, String fieldReplacementTable) {
		this.bugName = bugName;
		this.afClass = afClass;
		this.afName = afName;
		this.fieldAccess = fieldAccess;
		this.cmSig = cmSig;
		this.fieldReplacementTable = fieldReplacementTable;
	}
	
	// bug_name TEXT, af_class TEXT, af_name TEXT, field_access TEXT, cm TEXT,
	// rp_type TEXT, old_entity TEXT, new_entity TEXT
	public void execute(String rpType, String oldEntity, String newEntity) {
		Connection conn = SqliteManager.getConnection();
		try {
			PreparedStatement ps = conn.prepareStatement("INSERT INTO " + fieldReplacementTable
					+ " (bug_name,af_class,af_name,field_access,cm,rp_type,old_entity,new_entity) "
					+ "VALUES (?,?,?,?,?,?,?,?)");
			ps.setString(1, bugName);
			ps.setString(2, afClass);
			ps.setString(3, afName);
			ps.setString(4, fieldAccess);
			ps.setString(5, cmSig);
			ps.setString(6, rpType);
			ps.setString(7, oldEntity);
			ps.setString(8, newEntity);
			ps.executeUpdate();
			ps.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
		}
	}
}
