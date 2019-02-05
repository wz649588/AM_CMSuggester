package edu.vt.cs.prediction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Scanner;

/**
 * Process variable names
 * 
 * @author Ye Wang
 * @since 02/10/2017
 */
public class NameProcessor {
	/**
	 * It splits a variable name which can contains letters, digits, underscores "_", 
	 * but it cannot handle dollar signs "$" properly.
	 * @param v variable name string
	 * @return list of split words of variable name
	 */
	public static List<String> split(String v) {
		List<String> splitWords = new ArrayList<String>();
		
		if (v == null || v.isEmpty())
			return splitWords;
		
		if (v.toUpperCase().equals(v)) {
			// only contains "_", upper case letters and numbers
			// AAA_AAA_AAA, _AA_AA, AA_AA_, _AA_AA2
			Scanner scanner = new Scanner(v);
			scanner.useDelimiter("_");
			while (scanner.hasNext()) {
				splitWords.add(scanner.next());
			}
			scanner.close();
		} else if (v.contains("_")) {
			// aaa_aaa, AA_aaAaa
			Scanner scanner = new Scanner(v);
			scanner.useDelimiter("_");
			while (scanner.hasNext()) {
				splitWords.addAll(splitCamel(scanner.next()));
			}
			scanner.close();
		} else {
			return splitCamel(v);
		}
		
		return splitWords;
	}
	
	/**
	 * A2 => A, 2
	 * getXML2 => get, XML, 2
	 * get123 => get, 123
	 * apple2Orange => apple, 2, Orange
	 * The input variable name must not be empty or null.
	 * @param v variable name string
	 * @return list of split words of variable name
	 */
	private static List<String> splitCamel(String v) {
		List<String> splitWords = new ArrayList<String>();
		int wordHead = 0;
		int i = 0;
		while (i < v.length()) {
			
			char ch = v.charAt(i);
			if (Character.isDigit(ch)) {
				int digitLength = 1;
				for (int j = i + 1; j < v.length(); j++) {
					if (Character.isDigit(v.charAt(j))) {
						digitLength++;
					} else {
						break;
					}
				}
				
				if (wordHead < i) {
					String prevWords = v.substring(wordHead, i);
					splitWords.addAll(splitCamelWithNoDigit(prevWords));
				}
				splitWords.add(v.substring(i, i + digitLength));
				wordHead = i + digitLength;
				
				
				i += digitLength;
			} else {
				i++;
			}
			
		}
		if (wordHead < v.length())
			splitWords.addAll(splitCamelWithNoDigit(v.substring(wordHead)));
		return splitWords;
	}
	
	/**
	 * Deal with camel case variable names, like aaaAaaAaa, aaaABCAaa, AaaAaaAaa.
	 * The input variable name must not contain any underscore "_" or any digit.
	 * The input variable name must not be empty or null.
	 * aaaAAABaa => aaa, AAA, Baa.
	 * aaaAAAB => aaa, AAAB.
	 * @param v variable name string
	 * @return list of split words of variable name
	 */
	private static List<String> splitCamelWithNoDigit(String v) {
		// Doesn't contain "_"
		// aaaAaaAaa, aaaABCAaa, AaaAaaAaa
		// Think numbers and lower case letters are the same. 
		
		List<String> splitWords = new ArrayList<String>();
		
		Deque<Integer> endpointIndices = new ArrayDeque<Integer>();
		// The first split index is 0
		endpointIndices.add(0);
		boolean hasNextWord = false;
		do {
			hasNextWord = false;
			int lastPoint = endpointIndices.getLast();
			for (int i = lastPoint + 1; i < v.length(); i++) {
				if (((Character.isLowerCase(v.charAt(i - 1)) || Character.isDigit(v.charAt(i - 1))) && Character.isUpperCase(v.charAt(i))) ||
						Character.isUpperCase(v.charAt(i)) && i + 1 < v.length() && !Character.isUpperCase(v.charAt(i + 1))
						
						) {
					// aaAA => aa, AA
					// aaAABaa => aa, AA, Baa
					// aaAa => aa, Aa
					// aaA => aa, A
					hasNextWord = true;
					endpointIndices.add(i);
					break;
				}
			}
		} while (hasNextWord);
		endpointIndices.add(v.length());
		
		Iterator<Integer> endpointIterator = endpointIndices.iterator();
		int wordHead = endpointIterator.next();
		while (endpointIterator.hasNext()) {
			int wordTail = endpointIterator.next();
			String word = v.substring(wordHead, wordTail);
			splitWords.add(word);
			wordHead = wordTail;
		}
		
		return splitWords;
	}
	
}
