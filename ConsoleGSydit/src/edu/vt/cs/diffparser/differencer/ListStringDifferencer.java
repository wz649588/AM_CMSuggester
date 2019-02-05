package edu.vt.cs.diffparser.differencer;

import edu.vt.cs.diffparser.astdiff.treematching.measure.NGramsCalculator;

public class ListStringDifferencer extends ListDifferencer<String>{

	NGramsCalculator calc = new NGramsCalculator();
	
	@Override
	public boolean isMatched(String left, String right) {
		return calc.isMatched(left, right);
	}

}
