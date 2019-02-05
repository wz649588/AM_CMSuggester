package edu.vt.cs.prediction.ml;

public class JsonNameAnalysis {
	
	public int afUniqueWordNum;
	
	/**
	 * In the method, the number of words that is identical to an AF word (ignore cases)
	 */
	public int relevantWordNumInMethod;
	
	/**
	 * Numbers of identifiers sharing words with AF.
	 * [0] number of identifiers that shares 1 common word with AF
	 * [1] number of identifiers that shares 2 common words with AF 
	 * [2] number of identifiers that shares 3 common words with AF 
	 * ...
	 */
	public int[] similarIdentifierNums;
}
