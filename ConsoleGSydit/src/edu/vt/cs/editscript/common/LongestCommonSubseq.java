package edu.vt.cs.editscript.common;

import java.util.ArrayList;
import java.util.List;

/**
 * Solve the longest common subsequence problem. 
 * This is a dynamic programming implementation.
 * @author Ye Wang
 * @since 03/26/2017
 * @param <T> type of the list member
 */
public class LongestCommonSubseq<T> {
//	private List<T> leftList;
//	private List<T> rightList;
	
	public List<T> resultList;
//	private List<Integer> leftIndices;
//	private List<Integer> rightIndices; 
	
	public LongestCommonSubseq(List<T> A, List<T> B) {
//		this.leftList = A;
//		this.rightList = B;
		
		int[][] L = new int[A.size() + 1][B.size() + 1];
		for (int i = A.size(); i >= 0; i--) {
			for (int j = B.size(); j >= 0; j--) {
				if (i == A.size() || j == B.size()) L[i][j] = 0;
				else if (A.get(i).equals(B.get(j))) L[i][j] = 1 + L[i+1][j+1];
				else L[i][j] = Math.max(L[i+1][j], L[i][j+1]);
			}
		}
		// Here, L[0,0] is the length of LCS
		
		List<T> S = new ArrayList<>();
	    int i = 0;
	    int j = 0;
	    while (i < A.size() && j < B.size())
	    {
			if (A.get(i).equals(B.get(j)))
			{
//			    add A[i] to end of S;
			    S.add(A.get(i));
			    i++;
			    j++;
			}
			else if (L[i+1][j] >= L[i][j+1]) i++;
			else j++;
	    }
		
	    resultList = S;
	}
	
	public List<T> getResultList() {
		return resultList;
	}
	
//	public static void main(String[] args) {
//		String A = "ACBDEA";
//		String B = "ABCDA";
//		char asff = 'd';
//		
//		List<Character> l1 = new ArrayList<Character>();
//		List<Character> l2 = new ArrayList<Character>();	
//		
//		for (char c: A.toCharArray()) {
//			l1.add(c);
//		}
//		for (char c: B.toCharArray()) {
//			l2.add(c);
//		}
//		
//		LongestCommonSubseq<Character> lcs = new LongestCommonSubseq(l1, l2);
//		List<Character> result = lcs.resultList;
//		String s = "";
//		for (char c: result) {
//			s += c;
//		}
//		
//		System.out.println(s);
//	}
	


}
