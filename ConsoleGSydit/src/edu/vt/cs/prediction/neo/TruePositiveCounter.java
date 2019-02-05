package edu.vt.cs.prediction.neo;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.List;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.sql.SqliteManager;

public class TruePositiveCounter {
	
	private String table;
	
	private int tpCounter = 0;;
	
	private int accessPredictionInTpCounter = 0;

	public TruePositiveCounter(String table) {
		this.table = table;
	}
	
	public void execute() {
		Connection conn = SqliteManager.getConnection();
		Gson gson = new Gson();
		Type tpType = new TypeToken<List<String>>(){}.getType();
		Type accessType = new TypeToken<Map<String, Map<String, String>>>(){}.getType();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT tp, access_detail FROM " + table);
			while (rs.next()) {
				String tpJson = rs.getString(1);
				String accessJson = rs.getString(2);
				List<String> tp = gson.fromJson(tpJson, tpType);
				Map<String, Map<String, String>> accessDetailMap = gson.fromJson(accessJson, accessType);
				tpCounter += tp.size();
				for (Map<String, String> accessMap: accessDetailMap.values()) {
					String realAccess = accessMap.get("real");
					if (!realAccess.equals("none")) {
						accessPredictionInTpCounter++;
					}
				}
			}
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public int getTpNumber() {
		return tpCounter;
	}
	
	public int getAccessPredictionInTpNumber() {
		return accessPredictionInTpCounter;
	}
	
	public static void main(String[] args) {
		String[] tables = {"prediction_cm_neo_aries",
				"prediction_cm_neo_cassandra",
				"prediction_cm_neo_derby",
				"prediction_cm_neo_mahout"};
		
		int totalTp = 0;
		int totalAccess = 0;
		for (String table: tables) {
			TruePositiveCounter counter = new TruePositiveCounter(table);
			counter.execute();
			int tpNumber = counter.getTpNumber();
			int AccessPredictionInTpNumber = counter.getAccessPredictionInTpNumber();
			System.out.println(table);
			System.out.println(tpNumber);
			System.out.println(AccessPredictionInTpNumber);
			totalTp += tpNumber;
			totalAccess += AccessPredictionInTpNumber;
		}
		System.out.println("Total");
		System.out.println(totalTp);
		System.out.println(totalAccess);
	}
	
	
}
