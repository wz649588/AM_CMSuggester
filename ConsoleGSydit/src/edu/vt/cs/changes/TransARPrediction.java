package edu.vt.cs.changes;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.vt.cs.sql.SqliteManager;

public class TransARPrediction {
	public static String commitOrderTable;
	
	static final double minConfidence = 0.1;
	
	private static final boolean DEBUG = true;
	
	public static List<String> execute(List<String> evidenceMethods, String roseTable, String currentCommit) {
		Set<String> Q = new HashSet<String>();
		for(String method : evidenceMethods) {
			Q.add(method);
			System.out.println(currentCommit + " " + method);
		}
		HashMap<String, Integer> soloSupport = new HashMap<>();
		
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
			HashSet<String> orderBugSet = new HashSet<String>();
			stmt.close();
			
			stmt = conn.createStatement();
			
			ResultSet rsOrder = stmt.executeQuery("SELECT count(*) FROM (" + orderQuery + ")");
			rsOrder.next();
			int totalNum = rsOrder.getInt(1);
			stmt.close();
			
			for (int offset = 0; offset < totalNum; offset++) {
				stmt = conn.createStatement();
				
				rsOrder = stmt.executeQuery("SELECT bug_name FROM (" + orderQuery + ") LIMIT 1 OFFSET " + offset);
				String bugName = rsOrder.getString(1);
				orderBugSet.add(bugName);
				rsOrder.close();
				
				stmt.close();
			}
			System.out.println("The size of rsOrder is " + orderBugSet.size());
			
			
			
			stmt = conn.createStatement();
			
			Map<String, HashSet<String>> historyTrans = new HashMap<String, HashSet<String>>();
			HashMap<String, Integer> mI = new HashMap<>();
			HashMap<Integer, String> iM = new HashMap<>();
			int index = 0;
			
			ResultSet rsTrans = stmt.executeQuery("SELECT count(*) FROM " + roseTable);
			rsTrans.next();
			totalNum = rsTrans.getInt(1);
			stmt.close();
			for (int offset = 0; offset < totalNum; offset++) {
				stmt = conn.createStatement();
				
				rsTrans = stmt.executeQuery("SELECT bug_name, old_name FROM " + roseTable + " LIMIT 1 OFFSET " + offset);
				String bugName = rsTrans.getString(1);
				String oldName = rsTrans.getString(2);
				if (!orderBugSet.contains(bugName)) continue;
				if (!historyTrans.containsKey(bugName)){
					historyTrans.put(bugName, new HashSet<String>());
				}
				historyTrans.get(bugName).add(oldName);
				if (!soloSupport.containsKey(oldName)) {
					soloSupport.put(oldName, 0);
					mI.put(oldName, index);
					iM.put(index, oldName);
					index++;
				}
				soloSupport.put(oldName,  soloSupport.get(oldName) + 1);
				rsTrans.close();
				
				stmt.close();
			}
			
			double[][] regular = new double[index][index];
			
			
			for (HashSet<String> T : historyTrans.values()) {
				for (String method : T) {
					for (String otherMethod : T) {
						int from = mI.get(method);
						int to = mI.get(otherMethod);
						if (from != to) regular[from][to]++;
					}
				}
			}
			
			for (int i = 0; i < index; i++) {
				for (int j = 0; j < index; j++) {
					regular[i][j] /= soloSupport.get(iM.get(i));
				}
			}
			
//			double[][] association = new double[index][index];
//			
//			for (int i = 0; i < index; i++){
//				for (int j = 0; j < index; j++) {
//					if (i != j && regular[i][j] == 0) {
//						double temp = 0;
//						for (int k = 0; k < index; k++){
//							if (regular[i][k] != 0 && regular[k][j] != 0) {
//								temp = Math.max(temp, regular[i][k] * regular[k][j]);
//							}
//						}
//						association[i][j] = temp;
//					}
//				}
//			}
			
			for (String query : Q) {
				if (!soloSupport.containsKey(query)) continue;
				int from = mI.get(query);
				for (int i = 0; i < index; i++) {
					if (from == i) continue;
					if (regular[from][i] == 0) {
						double temp = 0;
						for (int k = 0; k < index; k++) {
							if (regular[from][k] != 0 && regular[k][i] != 0) {
								temp = Math.max(temp, regular[from][k] * regular[k][i]);
							}
						}
						if (temp > minConfidence && !result.contains(iM.get(i))) result.add(iM.get(i));
					}
					
					else if (regular[from][i] > minConfidence && !result.contains(iM.get(i))) result.add(iM.get(i));
				}
			}
			
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		return result;
	}
}
