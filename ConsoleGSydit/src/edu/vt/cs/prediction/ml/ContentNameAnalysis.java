package edu.vt.cs.prediction.ml;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.prediction.JsonTemplateEvidence;
import edu.vt.cs.prediction.NameProcessor;
import edu.vt.cs.sql.SqliteManager;

/**
 * This class analyzes the number of relevantWordNumInMethod and similarIdentifierNums
 * @author Ye Wang
 * @since 04/30/2017
 *
 */
public class ContentNameAnalysis {
	
	private static boolean executeFromScratch = true;

	public static void main(String[] args) throws SQLException {
		// link to database
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS prediction_cm_ml_name_stat");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS prediction_cm_ml_name_stat (tp_stat TEXT, fp_stat TEXT, fn_stat TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM prediction_cm");
		int totalRowNum = 0;
		if (rs.next())
			totalRowNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type evidenceList = new TypeToken<List<JsonTemplateEvidence>>(){}.getType();
//		Type statType = new TypeToken<List<JsonNameAnalysis>>(){}.getType();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO prediction_cm_ml_name_stat (tp_stat, fp_stat, fn_stat) VALUES (?,?,?)");
		
		for (int offset = 0; offset < totalRowNum; offset++) {
			rs = stmt.executeQuery("SELECT af_name, tp_vars, fp_vars, fn_vars FROM prediction_cm LIMIT 1 OFFSET " + offset);
			String afName = rs.getString("af_name");
			String tpVars = rs.getString("tp_vars");
			String fpVars = rs.getString("fp_vars");
			String fnVars = rs.getString("fn_vars");
			rs.close();
			
			List<JsonTemplateEvidence> tpData = gson.fromJson(tpVars, evidenceList);
			List<JsonTemplateEvidence> fpData = gson.fromJson(fpVars, evidenceList);
			List<JsonTemplateEvidence> fnData = gson.fromJson(fnVars, evidenceList);
			
			// break down AF name, and get unique words.
			List<String> afWordList = NameProcessor.split(afName);
			Set<String> afWordSet = new HashSet<>();
			for (String afWord: afWordList) {
				afWordSet.add(afWord.toLowerCase());
			}
			
			List<JsonNameAnalysis> tpNameStat = analyzeMethodList(afWordSet, tpData);
			List<JsonNameAnalysis> fpNameStat = analyzeMethodList(afWordSet, fpData);
			List<JsonNameAnalysis> fnNameStat = analyzeMethodList(afWordSet, fnData);
			
			String jsonTpStat = gson.toJson(tpNameStat);
			String jsonFpStat = gson.toJson(fpNameStat);
			String jsonFnStat = gson.toJson(fnNameStat);
			
			ps.setString(1, jsonTpStat);
			ps.setString(2, jsonFpStat);
			ps.setString(3, jsonFnStat);
			ps.executeUpdate();
			
			
			
			
			
			
			/* Word level
			 * AF: w1, w2, w3, ...
			 * In a method, we use bag-of-word model.
			 * For fields, local variables, and methods, we have a table for each
			 * 
			 */
			
			
			// Identifier level
			
		}
		ps.close();
		
		conn.close();
	}
	
	private static List<JsonNameAnalysis> analyzeMethodList(Set<String> afWordSet, List<JsonTemplateEvidence> evidenceList) {
		List<JsonNameAnalysis> nameStat = new ArrayList<>(); 
		for (JsonTemplateEvidence evidence: evidenceList) {
			if (evidence == null)
				continue;
			JsonNameAnalysis nameAnalysis = new JsonNameAnalysis();
			nameAnalysis.afUniqueWordNum = afWordSet.size();
			nameAnalysis.relevantWordNumInMethod = analyzeInWordLevel(afWordSet, evidence);;
			nameAnalysis.similarIdentifierNums = analyzeInIdentifierLevel(afWordSet, evidence);
			nameStat.add(nameAnalysis);
		}
		return nameStat;
	}
	
	private static int analyzeInWordLevel(Set<String> afWordSet, JsonTemplateEvidence evidence) {
		List<String> allNames = new ArrayList<>();
		allNames.addAll(evidence.fieldNameList);
		allNames.addAll(evidence.localNameList);
		allNames.addAll(evidence.methodNameList);
		
		int relevantWordNumInMethod = 0;
		for (String name: allNames) {
			List<String> wordList = NameProcessor.split(name);
			for (String word: wordList) {
				for (String afWord: afWordSet) {
					if (word.equalsIgnoreCase(afWord)) {
						relevantWordNumInMethod++;
						break;
					}
				}
			}
		}
		
		return relevantWordNumInMethod;
	}
	
	private static int[] analyzeInIdentifierLevel(Set<String> afWordSet, JsonTemplateEvidence evidence) {
		List<String> allNames = new ArrayList<>();
		allNames.addAll(evidence.fieldNameList);
		allNames.addAll(evidence.localNameList);
		allNames.addAll(evidence.methodNameList);
		
		int[] similarIdentifierNums = new int[afWordSet.size()];
		for (int i = 0; i < afWordSet.size(); i++) {
			similarIdentifierNums[i] = 0;
		}
		
		for (String name: allNames) {
			List<String> wordList = NameProcessor.split(name);
			
			int similarIntNum = 0;
			for (String word: wordList) {
				for (String afWord: afWordSet) {
					if (word.equalsIgnoreCase(afWord)) {
						similarIntNum++;
						break;
					}
				}
			}
			if (similarIntNum > 0) {
				int index = similarIntNum - 1;
				similarIdentifierNums[index] = similarIdentifierNums[index] + 1;
			}
		}
		
		return similarIdentifierNums;
	}
}
