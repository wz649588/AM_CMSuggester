package edu.vt.cs.prediction.neo;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.sql.SqliteManager;

/**
 * Count methods that predict access mode, including correct and incorrect predictions
 * @author Ye Wang
 * @since 08/28/2017
 */
public class AllAccessPredictionCounter {
	
	private String tableName;
	
	private int predictionCounter = 0;
	
	public AllAccessPredictionCounter(String tableName) {
		this.tableName = tableName;
	}
	
	public void execute() {
		Connection conn = SqliteManager.getConnection();
		Type accessType = new TypeToken<Map<String, Map<String, String>>>(){}.getType();
		Gson gson = new Gson();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT access_detail FROM " + tableName);
			while (rs.next()) {
				String accessJson = rs.getString(1);
				Map<String, Map<String, String>> accessDetailMap = gson.fromJson(accessJson, accessType);
				predictionCounter += accessDetailMap.size();
			}
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.println(tableName);
		System.out.println(predictionCounter);
		
	}
	
	public int getNumber() {
		return predictionCounter;
	}

	public static void main(String[] args) {
		String[] tables = {"prediction_cm_neo_aries",
				"prediction_cm_neo_cassandra",
				"prediction_cm_neo_derby",
				"prediction_cm_neo_mahout"};
		
		int total = 0;
		for (String table: tables) {
			AllAccessPredictionCounter counter = new AllAccessPredictionCounter(table);
			counter.execute();
			total += counter.getNumber();
		}
		System.out.println("Total");
		System.out.println(total);
	}
}
