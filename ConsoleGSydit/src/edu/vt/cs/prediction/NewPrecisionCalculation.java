package edu.vt.cs.prediction;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.sql.SqliteManager;

public class NewPrecisionCalculation {
	
	private static String tableName = "prediction_cm";

	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM " + tableName);
		int totalRow = 0;
		if (rs.next())
			totalRow = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type listType = new TypeToken<List<String>>(){}.getType();
		
		int totalTp = 0;
		int totalPrediction = 0;
		
		for (int offset = 0; offset < totalRow; offset++) {
			rs = stmt.executeQuery("SELECT tp, fp FROM " + tableName + " LIMIT 1 OFFSET " + offset);
			String tpJson = rs.getString(1);
			String fpJson = rs.getString(2);
			rs.close();
			List<String> tp = gson.fromJson(tpJson, listType);
			List<String> fp = gson.fromJson(fpJson, listType);
			totalTp += tp.size();
			totalPrediction += tp.size() + fp.size();
		}
		
		stmt.close();
		conn.close();
		
		System.out.println("Total TP: " + totalTp);
		System.out.println("Total Prediction: " + totalPrediction);
		System.out.println((double)totalTp / totalPrediction);
	}

}
