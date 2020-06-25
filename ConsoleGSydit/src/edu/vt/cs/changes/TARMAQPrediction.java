package edu.vt.cs.changes;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import edu.vt.cs.sql.SqliteManager;

public class TARMAQPrediction {
	static final double minSupport = 0.1;
	
	static final double minConfidence = 0.1;
	
	private static final boolean DEBUG = true;
	
	public static String commitOrderTable;
	
	public static List<String> execute(List<String> evidenceMethods, String roseTable, String currentCommit) {
		Set<String> Q = new HashSet<String>();
		for(String method : evidenceMethods) {
			Q.add(method);
			System.out.println(currentCommit + " " + method);
		}
		
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
				rsTrans.close();
				
				stmt.close();
			}
			System.out.println(orderBugSet.size());
			System.out.println(historyTrans.size());
			
			List<HashSet<String>> Hf = new ArrayList<HashSet<String>>();
			List<HashSet<String>> H = new ArrayList<HashSet<String>>();
			int k = 0;
			for (HashSet<String> T : historyTrans.values()) {
				H.add(T);
				Set<String> inter = new HashSet<String>(T);
				inter.retainAll(Q);
				System.out.println("The size of intersection is " + inter.size());
				if (inter.size() > k) {
					k = inter.size();
					Hf = new ArrayList<HashSet<String>>();
					Hf.add(T);
				}
				else if (k > 0 && inter.size() == k) {
					Hf.add(T);
				}
			}
			
			HashSet<Rule> R = new HashSet<Rule>();
			HashMap<HashSet<String>, Integer> anteCon = new HashMap<>();
			
			
			for (HashSet<String> T : Hf) {
				HashSet<String> Qprime = new HashSet<String>(T);
				Qprime.retainAll(Q);
				for (String x : T) {
					if (Qprime.contains(x)) continue;
					Rule rule = new Rule(Qprime, x);
					if (!R.contains(rule)) {
						if (!anteCon.containsKey(Qprime)) {
							anteCon.put(Qprime, 0);
							for (HashSet<String> TT : H) {
								if (TT.containsAll(Qprime))  anteCon.put(Qprime, anteCon.get(Qprime) + 1);
							}
						}
						
						rule.fre++;
						rule.support++;
						rule.confidence = rule.fre * 1.0 / anteCon.get(Qprime);
						R.add(rule);
					}
					else {
						for (Rule r : R) {
							if (r.equals(rule)) {
								r.fre++;
								r.support++;
								r.confidence = r.fre * 1.0 / anteCon.get(Qprime);
							}
						}
					}
					
				}
				
			}
			
			/*
			 * Hf is the fileterd history transactions, H is the whole history.
			 * R contains all the rules with their fre, support, and confidence
			 */
			PriorityQueue<Rule> pq = new PriorityQueue<Rule> (R.size() + 1, new Rank());
			for(Rule r : R) {
				pq.offer(r);
			}
			int maxSupport = -1;
			while (!pq.isEmpty()) {
				Rule r = pq.poll();
				System.out.println(r.confidence);
				System.out.println("The support is " + r.support);
				if(r.support > maxSupport) maxSupport = r.support;
//				double confidence = ((double) r.support) / maxSupport;
				if (r.confidence > minConfidence && !result.contains(r.consequence)) {
					
					result.add(r.consequence);
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

class Rule{
	HashSet<String> ante;
	String consequence;
	int fre = 0;
	int support = 0;
	double confidence = 0;
	public Rule(HashSet<String> ante, String consequence){
		this.ante = ante;
		this.consequence = consequence;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o == this) return true;
		if (!(o instanceof Rule)) return false;
		Rule c = (Rule) o;
		return ante.equals(c.ante) && consequence.equals(c.consequence);
	}
	
	@Override
	public int hashCode() {
		int hash = 17;
		hash = 31 * hash + ante.hashCode();
		hash = 31 * hash + consequence.hashCode();
		return hash;
	}
	
}

class Rank implements Comparator<Rule> {
	public int compare(Rule r1, Rule r2) {
		if (r1.support > r2.support) return -1;
		else if (r1.support < r2.support) return 1;
		else if (r1.confidence > r2.confidence) return -1;
		else if (r1.confidence < r2.confidence) return 1;
		return 0;
	}
}
