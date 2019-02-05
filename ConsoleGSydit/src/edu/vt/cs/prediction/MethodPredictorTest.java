package edu.vt.cs.prediction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class MethodPredictorTest {

	@SuppressWarnings("unchecked")
	@Test
	public void testExtractCommonWordIndices() {
		List<List<Object>> examples = new ArrayList<List<Object>>();
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("old", "Name", "Processor"),
						Arrays.<String>asList("new", "Name", "Processor"),
						new int[][]{{1, 2}},
						new int[][]{{1, 2}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old", "Name"),
						Arrays.<String>asList("my", "New", "Name"),
						new int[][]{{0}, {2}},
						new int[][]{{0}, {2}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old"),
						Arrays.<String>asList("my", "New"),
						new int[][]{{0}},
						new int[][]{{0}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old", "Name"),
						Arrays.<String>asList("your", "Name"),
						new int[][]{{2}},
						new int[][]{{1}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my"),
						Arrays.<String>asList("your", "New"),
						new int[0][0],
						new int[0][0]
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Name"),
						Arrays.<String>asList("my", "New", "Name"),
						new int[][]{{0}, {1}},
						new int[][]{{0}, {2}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Name"),
						Arrays.<String>asList("my", "my", "Name"),
						new int[][]{{0}, {1}},
						new int[][]{{0}, {2}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "aa", "Name", "is", "Jane", "Doe"),
						Arrays.<String>asList("my", "New", "Name", "is", "Mike", "bb", "Doe", "Jr"),
						new int[][]{{0}, {2, 3}, {5}},
						new int[][]{{0}, {2, 3}, {6}}
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "New"),
						Arrays.<String>asList("your", "my", "New"),
						new int[][]{{0, 1}},
						new int[][]{{1, 2}}
				));
		
		for (List<Object> example: examples) {
			List<String> afWords = (List<String>) example.get(0);
			List<String> varWords = (List<String>) example.get(1);
			int[][] afCommonsExpectedOriginal = (int[][]) example.get(2);
			int[][] varCommonsExpectedOriginal = (int[][]) example.get(3);
			
			List<List<Integer>> afCommonsExpected = new ArrayList<>();
			for (int[] afPiece: afCommonsExpectedOriginal) {
				List<Integer> afCommon = new ArrayList<Integer>();
				for (int i: afPiece) {
					afCommon.add(i);
				}
				afCommonsExpected.add(afCommon);
			}
			
			List<List<Integer>> varCommonsExpected = new ArrayList<>();
			for (int[] varPiece: varCommonsExpectedOriginal) {
				List<Integer> varCommon = new ArrayList<Integer>();
				for (int i: varPiece) {
					varCommon.add(i);
				}
				varCommonsExpected.add(varCommon);
			}
			
			List<List<List<Integer>>> result = MethodPredictor.extractCommonWordIndices(afWords, varWords);
			List<List<Integer>> afCommonsActual = result.get(0);
			List<List<Integer>> varCommonsActual = result.get(1);
			
			assertEquals(afCommonsExpected, afCommonsActual);
			assertEquals(varCommonsExpected, varCommonsActual);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testInduceTemplate() {
		
		List<List<Object>> examples = new ArrayList<>();
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old"),
						Arrays.<String>asList("your", "New"),
						Collections.<String>emptyList()
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "aa", "Name", "is", "Jane", "Doe"),
						Arrays.<String>asList("my", "New", "Name", "is", "Mike", "bb", "Doe", "Jr"),
						Arrays.<String>asList("my", "*1", "Name", "is", "*1+", "Doe", "*0+")
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old", "Name"),
						Arrays.<String>asList("my", "New", "Name"),
						Arrays.<String>asList("my", "*1", "Name")
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old"),
						Arrays.<String>asList("my", "New"),
						Arrays.<String>asList("my", "*1")
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "Old"),
						Arrays.<String>asList("my"),
						Arrays.<String>asList("my", "*0+")
				));
		examples.add(
				Arrays.<Object>asList(
						Arrays.<String>asList("my", "New"),
						Arrays.<String>asList("your", "my", "New"),
						Arrays.<String>asList("*0+", "my", "New")
				));
		
		for (List<Object> e: examples) {
			List<String> afWords = (List<String>) e.get(0);
			List<String> varWords = (List<String>) e.get(1);
			List<List<List<Integer>>> result = MethodPredictor.extractCommonWordIndices(afWords, varWords);
			List<List<Integer>> afCommons = result.get(0);
			List<List<Integer>> varCommons = result.get(1);
			List<String> templateExpected  = (List<String>) e.get(2);
			List<String> templateActual = MethodPredictor.induceTemplate(afWords, varWords, afCommons, varCommons);
			assertEquals(templateExpected, templateActual);
		}
		
	}
	
	

	@Test
	public void testMergeTemplates() {
		List<List<Object>> examples = new ArrayList<>();
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"match", "*", "random"}, {"match", "*", "random", "*"}},
						new String[][]{{"a1", "a2"}, {"b1", "b2"}},
						new String[][]{{"match", "*", "random", "*"}},
						new String[][]{{"a1", "a2", "b1", "b2"}}
				));
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"*", "match", "*", "random"}, {"match", "*", "random", "*"}},
						new String[][]{{"c1", "c2"}, {"b2"}},
						new String[][]{{"*", "match", "*", "random", "*"}},
						new String[][]{{"c1", "c2", "b2"}}
				));
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"match"}, {"match", "*"}},
						new String[][]{{"d1", "a2"}, {"g1"}},
						new String[][]{{"match", "*"}},
						new String[][]{{"d1", "a2", "g1"}}
				));
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"match"}, {"*", "match"}},
						new String[][]{{"p1", "a2"}, {"g1"}},
						new String[][]{{"*", "match"}},
						new String[][]{{"p1", "a2", "g1"}}
				));
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"match"}, {"*", "match"}, {"rf", "*"}},
						new String[][]{{"p1", "a2"}, {"g1"}, {"f"}},
						new String[][]{{"*", "match"}, {"rf", "*"}},
						new String[][]{{"p1", "a2", "g1"}, {"f"}}
				));
		examples.add(
				Arrays.<Object>asList(
						new String[][]{{"match"}, {"*", "match"}, {"rf", "*"}, {"*", "rf", "*"}},
						new String[][]{{"p1", "a2"}, {"g1"}, {"f"}, {"gou", "li"}},
						new String[][]{{"*", "match"}, {"*", "rf", "*"}},
						new String[][]{{"p1", "a2", "g1"}, {"f", "gou", "li"}}
				));
		
		for (List<Object> e: examples) {
			String[][] inputTemplates0 = (String[][]) e.get(0);
			String[][] inputVarLists0 = (String[][]) e.get(1);
			String[][] expectedTemplates0 = (String[][]) e.get(2);
			String[][] expectedVarList0 = (String[][]) e.get(3);
			
			Map<List<String>, List<String>> input = new HashMap<>();
			for (int i = 0; i < inputTemplates0.length; i++) {
				List<String> inputTemplate = Arrays.asList(inputTemplates0[i]);
				List<String> inputVarList = Arrays.asList(inputVarLists0[i]);
				input.put(inputTemplate, inputVarList);
			}
			
			Map<List<String>, List<String>> actualOutput = MethodPredictor.mergeTemplates(input);
			
			for (int i = 0; i < expectedTemplates0.length; i++) {
				List<String> expectedTemplate = Arrays.asList(expectedTemplates0[i]);
				Set<String> expectedVarSet = new HashSet<>(Arrays.asList(expectedVarList0[i]));
				if (actualOutput.containsKey(expectedTemplate)) {
					Set<String> actualVarSet = new HashSet<>(actualOutput.get(expectedTemplate));
					assertTrue(expectedVarSet.equals(actualVarSet));
				} else {
					fail(String.format("No expected template %s", expectedTemplate.toString()));
				}
			}
			
			
			
		}
	}
}
