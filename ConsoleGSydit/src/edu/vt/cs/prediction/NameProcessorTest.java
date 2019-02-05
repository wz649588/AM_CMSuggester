package edu.vt.cs.prediction;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

public class NameProcessorTest {

	@Test
	public void testSplit() {
		Map<String, List<String>> map = new HashMap<>();
		map.put("_ComplexAce_1pL", Arrays.asList("Complex", "Ace", "1", "p", "L"));
		map.put("ComplexAce_P", Arrays.asList("Complex", "Ace", "P"));
		map.put(null, Collections.<String>emptyList());
		map.put("", Collections.<String>emptyList());
		map.put("__Ace3CD", Arrays.asList("Ace", "3", "CD"));
		map.put("THIS_IS_A_TEST", Arrays.asList("THIS", "IS", "A", "TEST"));
		map.put("getXMLOutput", Arrays.asList("get", "XML", "Output"));
		map.put("a2", Arrays.asList("a", "2"));
		map.put("ComplexAce_1", Arrays.asList("Complex", "Ace", "1"));
		map.put("getXML", Arrays.asList("get", "XML"));
		map.put("getXML1", Arrays.asList("get", "XML", "1"));
		map.put("bus2AirHot", Arrays.asList("bus", "2", "Air", "Hot"));
		map.put("12afAce", Arrays.asList("12", "af", "Ace"));
		
		for (String v: map.keySet()) {
			List<String> expected = map.get(v);
			List<String> actual = NameProcessor.split(v);
			assertEquals(actual.size(), expected.size());
			for (int i = 0; i < actual.size(); i++) {
				assertEquals(v, expected.get(i), actual.get(i));
			}
		}
	}
	
}
