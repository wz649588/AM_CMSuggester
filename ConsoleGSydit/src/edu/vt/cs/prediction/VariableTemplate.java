package edu.vt.cs.prediction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * This class represents a template between an added field (AF)
 * and some variables in a method.
 * @author Ye Wang
 * @since 04/09/2017
 *
 */
public class VariableTemplate {
	
	/**
	 * List of stop words, which should not count in calculation
	 * of number and length of the template.
	 */
	public static List<String> stopWords = Arrays.asList("in");
	
	private List<String> template;
	
	/**
	 * Words in the template which are not wildcards
	 */
	private List<String> deterministicWords;
	
	/**
	 * Variables in a method that share this template with AF
	 */
	private List<String> similarVars;
	
	private Integer numberOfSimilarVars = null;
	
	private Integer numberOfDeterministicWords = null;
	
	/**
	 * E.g. 7 for {"abc", "Abcd"}
	 */
	private Integer totalLengthOfDeterministicWords = null;
	
//	private String rating;
	
	public VariableTemplate(List<String> template, List<String> similarVars) {
		this.template = template;
		this.similarVars = similarVars;
		
		this.deterministicWords = new ArrayList<>();
		for (String w: template) {
			if (!w.startsWith("*") && !isStopWord(w))
				deterministicWords.add(w);
		}
	}
	
	private static boolean isStopWord(String s) {
		for (String stop: stopWords) {
			if (stop.equalsIgnoreCase(s))
				return true;
		}
		return false;
	}
	
	public List<String> getTemplate() {
		return template;
	}
	
	public List<String> getSimilarVars() {
		return similarVars;
	}
	
	public int getNumberOfSimilarVars() {
		if (numberOfSimilarVars == null)
			numberOfSimilarVars = similarVars.size();
		return numberOfSimilarVars;
	}
	
	
	public int getNumberOfDeterministicWords() {
		if (numberOfDeterministicWords == null)
			numberOfDeterministicWords = deterministicWords.size();
		return numberOfDeterministicWords;
	}
	
	public int getTotalLengthOfDeterministicWords() {
		if (totalLengthOfDeterministicWords == null) {
			int length = 0;
			for (String w: deterministicWords) {
				length += w.length();
			}
			totalLengthOfDeterministicWords = length;
		}
		return totalLengthOfDeterministicWords;
	}
	
	/**
	 * Check whether the method with this template should use AF
	 * @return result of checking
	 */
	public boolean isSignificant() {
		if (getNumberOfSimilarVars() >= 2) {
			if (getNumberOfDeterministicWords() >= 2)
				return true;
			if (getTotalLengthOfDeterministicWords() >= 5)
				return true;
		}
		return false;
	}
	
	/**
	 * Check if a method with these templates should use AF
	 * @param tList list of templates
	 * @return result of checking
	 */
	public static boolean isSignificant(List<VariableTemplate> tList) {
		List<VariableTemplate> potentials = new ArrayList<>();
		for (VariableTemplate t: tList) {
			if (t.getNumberOfDeterministicWords() >= 2 || t.getTotalLengthOfDeterministicWords() >= 4)
				potentials.add(t);
		}
		return (potentials.size() >= 3);
	}
	
	public static List<VariableTemplate> extractWeakEvidence(List<VariableTemplate> tList) {
		List<VariableTemplate> weak = new ArrayList<>();
		for (VariableTemplate t: tList) {
			if (t.getNumberOfDeterministicWords() >= 2 || t.getTotalLengthOfDeterministicWords() >= 4)
				weak.add(t);
		}
		return weak;
	}
	
}
