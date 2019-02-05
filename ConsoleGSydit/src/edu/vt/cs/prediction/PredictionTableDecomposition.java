package edu.vt.cs.prediction;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.sql.SqliteManager;

/**
 * We want to observe every method in database table prediction_cm. However,
 * multiple method names are in the same table cell, which makes it hard to
 * read. This class will break down these cells into smaller cells. The original
 * table will be preserved, and the data will be stored in a new table whose
 * name is prediction_cm_decompose. 
 * @author Vito
 * @since 05/11/2017
 */
public class PredictionTableDecomposition {
	
	private static boolean executeFromScratch = true;

	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch) 
			stmt.executeUpdate("DROP TABLE IF EXISTS prediction_cm_decompose");
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS prediction_cm_decompose (bug_name TEXT,af_class TEXT,af_name TEXT,field_access TEXT,predict_type TEXT,method_name TEXT,decisive_template TEXT,evidence TEXT)");
		
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM prediction_cm");
		int totalRowNum = 0;
		if (rs.next())
			totalRowNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type listType = new TypeToken<List<String>>(){}.getType();
		Type evidenceType = new TypeToken<List<JsonTemplateEvidence>>(){}.getType();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO prediction_cm_decompose (bug_name,af_class,af_name,field_access,predict_type,method_name,decisive_template,evidence) VALUES (?,?,?,?,?,?,?,?)");
		
		for (int offset = 0; offset < totalRowNum; offset++) {
			rs = stmt.executeQuery("SELECT bug_name,af_class,af_name,field_access,decisive_template,tp,tp_vars,fp,fp_vars,fn,fn_vars FROM prediction_cm LIMIT 1 OFFSET " + offset);
			String bugName = rs.getString("bug_name");
			String afClass = rs.getString("af_class");
			String afName = rs.getString("af_name");
			String fieldAccess = rs.getString("field_access");
			String decisiveTemplate = rs.getString("decisive_template");
			String tpJson = rs.getString("tp");
			String tpVarsJson = rs.getString("tp_vars");
			String fpJson = rs.getString("fp");
			String fpVarsJson = rs.getString("fp_vars");
			String fnJson = rs.getString("fn");
			String fnVarsJson = rs.getString("fn_vars");
			
			ps.setString(1, bugName);
			ps.setString(2, afClass);
			ps.setString(3, afName);
			ps.setString(4, fieldAccess);
			ps.setString(7, decisiveTemplate);
			
			List<String> tp = gson.fromJson(tpJson, listType);
			List<String> fp = gson.fromJson(fpJson, listType);
			List<String> fn = gson.fromJson(fnJson, listType);
			
			List<JsonTemplateEvidence> tpVars = gson.fromJson(tpVarsJson, evidenceType);
			List<JsonTemplateEvidence> fpVars = gson.fromJson(fpVarsJson, evidenceType);
			List<JsonTemplateEvidence> fnVars = gson.fromJson(fnVarsJson, evidenceType);
			
			ps.setString(5, "TP");
			for (String methodName: tp) {
				ps.setString(6, methodName);
				JsonTemplateEvidence evidence = findEvidence(tpVars, methodName);
				String jsonEvidence = gson.toJson(evidence);
				ps.setString(8, jsonEvidence);
				ps.executeUpdate();
			}
			
			ps.setString(5, "FP");
			for (String methodName: fp) {
				ps.setString(6, methodName);
				JsonTemplateEvidence evidence = findEvidence(fpVars, methodName);
				String jsonEvidence = gson.toJson(evidence);
				ps.setString(8, jsonEvidence);
				ps.executeUpdate();
			}
			
			ps.setString(5, "FN");
			for (String methodName: fn) {
				ps.setString(6, methodName);
				JsonTemplateEvidence evidence = findEvidence(fnVars, methodName);
				String jsonEvidence = gson.toJson(evidence);
				ps.setString(8, jsonEvidence);
				ps.executeUpdate();
			}
			
			
			
			
			
		}
		
		ps.close();
		stmt.close();
		conn.close();
			
		
	}
	
	private static JsonTemplateEvidence findEvidence(List<JsonTemplateEvidence> evidenceList, String methodSig) {
		if (methodSig == null)
			return null;
		for (JsonTemplateEvidence e: evidenceList) {
			if (e == null)
				continue;
			if (methodSig.equals(e.name))
				return e;
		}
		return null;
	}

}
