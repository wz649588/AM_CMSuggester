package edu.vt.cs.prediction.ml;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.prediction.JsonTemplateEvidence;
import edu.vt.cs.sql.SqliteManager;

public class ContentNameAnalysisStat {

	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM prediction_cm_ml_name_stat");
		int totalRowNum = 0;
		if (rs.next())
			totalRowNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type statType = new TypeToken<List<JsonNameAnalysis>>(){}.getType();
		
		int tpNum = 0;
		int fpNum = 0;
		int fnNum = 0;
		
		int tpTotalRelevantWordNum = 0;
		int fpTotalRelevantWordNum = 0;
		int fnTotalRelevantWordNum = 0;
		
		int tpMaxAfUniqueWordNum = 0;
		int fpMaxAfUniqueWordNum = 0;
		int fnMaxAfUniqueWordNum = 0;
		
		

		for (int offset = 0; offset < totalRowNum; offset++) {
			rs = stmt.executeQuery("SELECT tp_stat, fp_stat, fn_stat FROM prediction_cm_ml_name_stat LIMIT 1 OFFSET "+ offset);
			String jsonTpStat = rs.getString(1);
			String jsonFpStat = rs.getString(2);
			String jsonFnStat = rs.getString(3);
			rs.close();
			
			List<JsonNameAnalysis> tpStatList = gson.fromJson(jsonTpStat, statType);
			List<JsonNameAnalysis> fpStatList = gson.fromJson(jsonFpStat, statType);
			List<JsonNameAnalysis> fnStatList = gson.fromJson(jsonFnStat, statType);
			
			
			for (JsonNameAnalysis tpStat: tpStatList) {
				tpNum++;
				tpTotalRelevantWordNum += tpStat.relevantWordNumInMethod;
				if (tpStat.afUniqueWordNum > tpMaxAfUniqueWordNum)
					tpMaxAfUniqueWordNum = tpStat.afUniqueWordNum;
				
			}
			for (JsonNameAnalysis fpStat: fpStatList) {
				fpNum++;
				fpTotalRelevantWordNum += fpStat.relevantWordNumInMethod;
				if (fpStat.afUniqueWordNum > fpMaxAfUniqueWordNum)
					fpMaxAfUniqueWordNum = fpStat.afUniqueWordNum;
			}
			for (JsonNameAnalysis fnStat: fnStatList) {
				fnNum++;
				fnTotalRelevantWordNum += fnStat.relevantWordNumInMethod;
				if (fnStat.afUniqueWordNum > fnMaxAfUniqueWordNum)
					fnMaxAfUniqueWordNum = fnStat.afUniqueWordNum;
			}
		}
		

		List<Integer> tpTotalSimilarIdentifierNums = new ArrayList<>();
		List<Integer> fpTotalSimilarIdentifierNums = new ArrayList<>();
		List<Integer> fnTotalSimilarIdentifierNums = new ArrayList<>();
		
		for (int i = 0; i < tpMaxAfUniqueWordNum; i++) {
			tpTotalSimilarIdentifierNums.add(0);
		}
		for (int i = 0; i < fpMaxAfUniqueWordNum; i++) {
			fpTotalSimilarIdentifierNums.add(0);
		}
		for (int i = 0; i < fnMaxAfUniqueWordNum; i++) {
			fnTotalSimilarIdentifierNums.add(0);
		}
		
		for (int offset = 0; offset < totalRowNum; offset++) {
			rs = stmt.executeQuery("SELECT tp_stat, fp_stat, fn_stat FROM prediction_cm_ml_name_stat LIMIT 1 OFFSET "+ offset);
			String jsonTpStat = rs.getString(1);
			String jsonFpStat = rs.getString(2);
			String jsonFnStat = rs.getString(3);
			rs.close();
			
			List<JsonNameAnalysis> tpStatList = gson.fromJson(jsonTpStat, statType);
			List<JsonNameAnalysis> fpStatList = gson.fromJson(jsonFpStat, statType);
			List<JsonNameAnalysis> fnStatList = gson.fromJson(jsonFnStat, statType);
			
			for (JsonNameAnalysis tpStat: tpStatList) {
				int[] tpSimilars = tpStat.similarIdentifierNums;
				for (int i = 0; i < tpSimilars.length; i++) {
					tpTotalSimilarIdentifierNums.set(i, tpTotalSimilarIdentifierNums.get(i) + tpSimilars[i]);
				}
			}
			for (JsonNameAnalysis fpStat: fpStatList) {
				int[] fpSimilars = fpStat.similarIdentifierNums;
				for (int i = 0; i < fpSimilars.length; i++) {
					fpTotalSimilarIdentifierNums.set(i, fpTotalSimilarIdentifierNums.get(i) + fpSimilars[i]);
				}
			}
			for (JsonNameAnalysis fnStat: fnStatList) {
				int[] fnSimilars = fnStat.similarIdentifierNums;
				for (int i = 0; i < fnSimilars.length; i++) {
					fnTotalSimilarIdentifierNums.set(i, fnTotalSimilarIdentifierNums.get(i) + fnSimilars[i]);
				}
			}
			
		}
		
		stmt.close();
		conn.close();
		
		System.out.println("Word Level:");
		System.out.println("tp:");
		System.out.println((double)tpTotalRelevantWordNum / tpNum);
		System.out.println("fp:");
		System.out.println((double)fpTotalRelevantWordNum / fpNum);
		System.out.println("fn:");
		System.out.println((double)fnTotalRelevantWordNum / fnNum);
		
		System.out.println();
		
		List<Double> tpAvgSimilarIdentifierNums = new ArrayList<>();
		List<Double> fpAvgSimilarIdentifierNums = new ArrayList<>();
		List<Double> fnAvgSimilarIdentifierNums = new ArrayList<>();
		
		for (Integer i: tpTotalSimilarIdentifierNums) {
			tpAvgSimilarIdentifierNums.add((double)i / tpNum);
		}
		for (Integer i: fpTotalSimilarIdentifierNums) {
			fpAvgSimilarIdentifierNums.add((double)i / fpNum);
		}
		for (Integer i: fnTotalSimilarIdentifierNums) {
			fnAvgSimilarIdentifierNums.add((double)i / fnNum);
		}
		
		System.out.println("Identifier Level:");
		System.out.println("tp:");
		System.out.println(tpAvgSimilarIdentifierNums);
		System.out.println("fp:");
		System.out.println(fpAvgSimilarIdentifierNums);
		System.out.println("fn:");
		System.out.println(fnAvgSimilarIdentifierNums);
		
		
	}
}
