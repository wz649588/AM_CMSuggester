package edu.vt.cs.prediction;

import static org.junit.Assert.assertArrayEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Checks whether a method should use an newly added field
 * @author Ye Wang
 * @since 02/22/2017
 */
public class MethodPredictor {
	
	/**
	 * Get var names sharing a pattern with AF name in a method
	 * @param af name of added field
	 * @param vars set of names of variables in a method
	 * @return set of variable names sharing a pattern with AF name
	 */
	public static Set<String> getPatternVars(String af, Set<String> vars) {
		// process the AF name
		List<String> afWords = NameProcessor.split(af);
//		ChunkList afChunkList = new ChunkList(afWords);
//		List<Chunk> afChunks = afChunkList.getChunks();
		
		// number of variable
		Set<String> patternVars = new HashSet<String>();
		
		for (String var: vars) {
			// process a variable name in the method
			List<String> varWords = NameProcessor.split(var);
//			ChunkList varChunkList = new ChunkList(varWords);
//			List<Chunk> varChunks = varChunkList.getChunks();
			
			// Check if the two names have common words in the heads or the tails
			// Scan onward
			List<String> onwardCommons = new ArrayList<String>();
			for (int i = 0; i < afWords.size() && i < varWords.size(); i++) {
				if (afWords.get(i).equals(varWords.get(i))) {
					onwardCommons.add(afWords.get(i));
				} else {
					break;
				}
			}
			
			// Scan backward
			List<String> backwardCommons = new ArrayList<String>();
			for (int j = 1; j <= afWords.size() && j <= varWords.size(); j++) {
				int afIndex = afWords.size() - j;
				int varIndex = varWords.size() - j;
				if (afWords.get(afIndex).equals(varWords.get(varIndex))) {
					backwardCommons.add(afWords.get(afIndex));
				} else {
					break;
				}
			}
			
			if (!onwardCommons.isEmpty() || !backwardCommons.isEmpty()) {
				patternVars.add(var);
			}
			
		}
		
		return patternVars;
	}
	
	/**
	 * <p>Extract templates between two variable names.</p>
	 * <p>The template may contain wildcards, the types of which are as follows:</p>
	 * <ul>
	 * <li>"*0+": zero words or more</li>
	 * <li>"*1+": one word or more</li>
	 * <li>"*1", "*2", "*3", etc.: 1, 2, 3, etc. word(s), at least one word</li>
	 * </ul>
	 * @param afName AF name
	 * @param varName variable name
	 * @return induced template, in List of String
	 */
	public static List<String> extractTemplate(String afName, String varName) {
		List<String> afWords = NameProcessor.split(afName);
		List<String> varWords = NameProcessor.split(varName);
		List<List<List<Integer>>> commonIndices = extractCommonWordIndices(afWords, varWords);
		List<List<Integer>> afCommons = commonIndices.get(0);
		List<List<Integer>> varCommons = commonIndices.get(1);
		return induceTemplate(afWords, varWords, afCommons, varCommons);
	}
	
	/**
	 * Extract the indices of common words between two variable names
	 * @param afWords pieces of AF name
	 * @param varWords pieces of variable name
	 * @return two list, first of which is AF common words indices, and second of which is var common words indices
	 */
	public static List<List<List<Integer>>> extractCommonWordIndices(List<String> afWords, List<String> varWords) {
		List<List<Integer>> afCommons = new ArrayList<>();
		List<List<Integer>> varCommons = new ArrayList<>();
		int varIndexFront = 0;
		for (int i = 0; i < afWords.size();) {
			String afCurrentWord = afWords.get(i);
			int commonLength = 0;
			for (int j = varIndexFront; j < varWords.size(); j++) {
				String varCurrentWord = varWords.get(j);
				if (afCurrentWord.equals(varCurrentWord)) {
					List<Integer> afPiece = new ArrayList<>();
					List<Integer> varPiece = new ArrayList<>();
					int afIndex = i;
					int varIndex = j;
					do {
						commonLength++;
						afPiece.add(afIndex);
						varPiece.add(varIndex);
						afIndex++;
						varIndex++;
						if (afIndex < afWords.size() && varIndex < varWords.size()) {
							afCurrentWord = afWords.get(afIndex);
							varCurrentWord = varWords.get(varIndex);
						}
					} while (afIndex < afWords.size() && varIndex < varWords.size() && afCurrentWord.equals(varCurrentWord));
					varIndexFront = varIndex;
					afCommons.add(afPiece);
					varCommons.add(varPiece);
					break;
				}
			}
			
			if (commonLength > 0) {
				i += commonLength;
			} else {
				i++;
			}
			
		}
		return Arrays.<List<List<Integer>>>asList(afCommons, varCommons);
	}
	
	/**
	 * <p>Induce name template from common words of variable names</p>
	 * <p>Wildcard types:<p>
	 * <ul>
	 * <li>"*0+": zero words or more</li>
	 * <li>"*1+": one word or more</li>
	 * <li>"*1", "*2", "*3", etc.: 1, 2, 3, etc. word(s), at least one word</li>
	 * </ul>
	 * @param afWords
	 * @param varWords
	 * @param afCommons
	 * @param varCommons
	 * @return induced template, in List of String
	 */
	public static List<String> induceTemplate(List<String> afWords, List<String> varWords, List<List<Integer>> afCommons, List<List<Integer>> varCommons) {
		
		if (afCommons.isEmpty())
			return Collections.<String>emptyList();
		
		// Generate template, insert wildcards
		List<String> template = new ArrayList<>();
		// check first
		List<Integer> afFirst = afCommons.get(0);
		List<Integer> varFirst = varCommons.get(0);
		String wildcard = generateWildcard(-1, afFirst.get(0), -1, varFirst.get(0));
		if (wildcard != null)
			template.add(wildcard);
		for (int afIndex: afFirst) {
			template.add(afWords.get(afIndex));
		}
		// check middle
		List<Integer> afNow = afFirst;
		List<Integer> varNow = varFirst;
		for (int i = 1; i < afCommons.size(); i++) {
			List<Integer> afPrev = afNow;
			List<Integer> varPrev = varNow;
			afNow = afCommons.get(i);
			varNow = varCommons.get(i);
			wildcard = generateWildcard(afPrev.get(afPrev.size() - 1), afNow.get(0), varPrev.get(varPrev.size() - 1), varNow.get(0));
			if (wildcard != null)
				template.add(wildcard);
			for (int afIndex: afNow) {
				template.add(afWords.get(afIndex));
			}
		}
		// check last
		List<Integer> afLast = afCommons.get(afCommons.size() - 1);
		List<Integer> varLast = varCommons.get(varCommons.size() - 1);
		wildcard = generateWildcard(afLast.get(afLast.size() - 1), afWords.size(), varLast.get(varLast.size() - 1), varWords.size());
		if (wildcard != null)
			template.add(wildcard);
		
		return template;
	}
	
	private static String generateWildcard(int afPrev, int afNow, int varPrev, int varNow) {
		String result;
		if (afPrev + 1 == afNow && varPrev + 1 == varNow) {
			// no wildcard
			result = null;
		} else if (afNow - afPrev == varNow - varPrev) {
			// fixed wildcard, one "*1" or more
			int wildcardNum = afNow - afPrev - 1;
			result = "*" + wildcardNum;
		} else if (afPrev + 1 == afNow || varPrev + 1 == varNow) {
			// zero words or more, "*0+"
			result = "*0+";
		} else {
			// one words or more, "*1+"
			result = "*1+";
		}
		
		return result;
	}
	
	/**
	 * Replace complex wildcards "*n", "*0+" and "*1+" with a simple "*" 
	 * @param t complex template
	 * @return simplified template
	 */
	public static List<String> simplifyTemplate(List<String> t) {
		List<String> result = new ArrayList<>();
		for (String w: t) {
			if (w.startsWith("*"))
				result.add("*");
			else
				result.add(w);
		}
		return result;
	}
	
	/**
	 * Merge *E*F* and E*F to *E*F*.
	 * Merge A*B* and A*B to A*B*.
	 * Merge *C*D and C*D to *C*D.
	 * 
	 * @param templateToVars
	 * @return merged templates
	 */
	public static Map<List<String>, List<String>> mergeTemplates(Map<List<String>, List<String>> templateToVars) {
		Map<List<String>, List<List<String>>> templateGroup = new HashMap<>();
		for (List<String> template: templateToVars.keySet()) {
			// force extend every template
			List<String> maximizedTemplate = new ArrayList<>();
			if (!template.get(0).equals("*"))
				maximizedTemplate.add("*");
			maximizedTemplate.addAll(template);
			if (!template.get(template.size() - 1).equals("*"))
				maximizedTemplate.add("*");
			// Group template
			if (!templateGroup.containsKey(maximizedTemplate)) {
				List<List<String>> group = new ArrayList<>();
				templateGroup.put(maximizedTemplate, group);
			}
			templateGroup.get(maximizedTemplate).add(template);
		}
		
		// Simplify maximized template
		Map<List<String>, List<List<String>>> simplifiedTemplateGroup = new HashMap<>();
		for (List<String> template: templateGroup.keySet()) {
			List<List<String>> groupedTemplates = templateGroup.get(template);
			List<String> simplifiedTemplate = new ArrayList<String>();
			boolean hasFirstWildcard = false;
			for (List<String> t: groupedTemplates) {
				if (t.get(0).equals("*")) {
					hasFirstWildcard = true;
					break;
				}
			}
			if (hasFirstWildcard) {
				simplifiedTemplate.add("*");
			}
			for (int i = 1; i < template.size() - 1; i++) {
				simplifiedTemplate.add(template.get(i));
			}
			boolean hasLastWildcard = false; 
			for (List<String> t: groupedTemplates) {
				if (t.get(t.size() - 1).equals("*")) {
					hasLastWildcard = true;
					break;
				}
			}
			if (hasLastWildcard) {
				simplifiedTemplate.add("*");
			}
			simplifiedTemplateGroup.put(simplifiedTemplate, groupedTemplates);
		}
		
		Map<List<String>, List<String>> resultMap = new HashMap<>();
		for (List<String> template: simplifiedTemplateGroup.keySet()) {
			List<List<String>> groupedTemplates = simplifiedTemplateGroup.get(template);
			List<String> vars = new ArrayList<>();
			for (List<String> t: groupedTemplates) {
				vars.addAll(templateToVars.get(t));
			}
			resultMap.put(template, vars);
		}
		
		
		return resultMap;
	}
	
}
