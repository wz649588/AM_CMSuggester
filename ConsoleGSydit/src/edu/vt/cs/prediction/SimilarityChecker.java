package edu.vt.cs.prediction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Scanner;

/**
 * Check the similarity of two variable name
 * 
 * @author Ye Wang
 * @since 02/08/2017
 */
public class SimilarityChecker {
	private String v1;
	private String v2;
	
	/**
	 * Construct a SimilarityChecker
	 * @param v1 one variable name
	 * @param v2 another variable name
	 */
	public SimilarityChecker(String v1, String v2) {
		this.v1 = v1;
		this.v2 = v2;
	}
	
	/**
	 * 
	 * @return true if two variable names are similar; otherwise false
	 */
	public boolean containsSimilarWord() {
		List<String> words1 = NameProcessor.split(v1);
		List<String> words2 = NameProcessor.split(v2);
		int similarNum = 0;
		for (String w1: words1) {
			for (String w2: words2) {
				if (w1.equals(w2)) {
					similarNum++;
					break;
				}
			}
		}
		return similarNum > 0;
	}
	
	
}
