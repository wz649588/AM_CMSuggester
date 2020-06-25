package edu.vt.cs.changes;

import java.util.HashMap;
import java.util.HashSet;
import java.util.PriorityQueue;

public class MapTest {
	public static void main(String[] args) {
		HashMap<HashSet<String>, Integer> anteCon = new HashMap<>();
		HashSet<String> a = new HashSet<>();
		a.add("a");
		a.add("b");
		anteCon.put(a, 2);
		HashSet<String> b = new HashSet<>();
		b.add("a");
		b.add("b");
		if(anteCon.containsKey(b)) {
			anteCon.put(b, anteCon.get(b) + 2);
		}
		System.out.println(anteCon.get(b));
		
		
		
		HashSet<Rule> R = new HashSet<Rule>();
		Rule rule1 = new Rule(a, "ruleA");
		rule1.fre++;
		rule1.support = 2;
		rule1.confidence = 0.3;
		R.add(rule1);
		Rule rule3 = new Rule(a, "ruleB");
		R.add(rule3);
		Rule rule2 = new Rule(b, "ruleA");
		System.out.println(R.contains(rule2));
		for(Rule r : R){
			if(r.equals(rule2)) {
				r.fre++;
				r.support = 3;
				r.confidence = 0.34;
			}
		}
		
		for(Rule r: R){
			System.out.println(r.consequence + " " + r.fre + " " + r.support);
		}
		
		
		PriorityQueue<Rule> queue = new PriorityQueue<Rule> (300, new Rank());
		
		Rule rule4 = new Rule(a, "ruleC");
		rule4.support = 4;
		rule4.confidence = 0.5;
		queue.add(rule1);
		queue.add(rule3);
		queue.add(rule4);
		while(!queue.isEmpty()){
			Rule r = queue.poll();
			System.out.println(r.consequence + " " + r.fre + " " + r.support + " " + r.confidence);
		}
		
		
		
	}
}

//class Rule{
//	HashSet<String> ante;
//	String consequence;
//	int fre = 0;
//	double support = 0;
//	double confidence = 0;
//	public Rule(HashSet<String> ante, String consequence){
//		this.ante = ante;
//		this.consequence = consequence;
//	}
//	
//	@Override
//	public boolean equals(Object o) {
//		if (o == this) return true;
//		if (!(o instanceof Rule)) return false;
//		Rule c = (Rule) o;
//		return ante.equals(c.ante) && consequence.equals(c.consequence);
//	}
//	
//	@Override
//	public int hashCode() {
//		int hash = 17;
//		hash = 31 * hash + ante.hashCode();
//		hash = 31 * hash + consequence.hashCode();
//		return hash;
//	}
//	
//}
