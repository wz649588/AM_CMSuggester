package edu.vt.cs.changes;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * 
 * @author Ye Wang
 * @since 04/22/2018
 *
 */
public class DivisionUtil {
	
	public static <T> Map<List<T>, List<T>> divide(Collection<T> input, int combinationSize) {
		List<T> list = new ArrayList<>(input);
		Combination<T> c = new Combination<>(list, combinationSize);
		c.execute();
		List<List<T>> combinations = c.getResult();
		Map<List<T>, List<T>> map = new LinkedHashMap<>();
		for (List<T> key: combinations) {
			List<T> value = new ArrayList<>(list);
			value.removeAll(key);
			map.put(key, value);
		}
		return map;
	}
	
	/**
	 * Just a test, this method can be deleted at any time
	 * @param args
	 */
	public static void main(String[] args) {
		int[] array = {1, 2, 3, 4, 5};
		List<Integer> list = new ArrayList<>();
		for (int i: array) {
			list.add(i);
		}
		Map<List<Integer>, List<Integer>> map = divide(list, 6);
		System.out.println(map);
		for (List<Integer> key: map.keySet()) {
			System.out.print(key);
			System.out.print(" -> ");
			System.out.println(map.get(key));
		}
	}
	
}

class Combination<T> {

	private List<T> list;
	
	private int combinationSize;
	
	private List<List<T>> result;
	
	Combination(List<T> list, int combinationSize) {
		this.list = list;
		this.combinationSize = combinationSize;
		result = new ArrayList<>();
	}
	
	void execute() {
		List<T> data = new ArrayList<>(Collections.<T>nCopies(combinationSize, null));
		privExecute(data, 0, list.size() - 1, 0);
	}
	
	private void privExecute(List<T> data, int start, int end, int index) {
		if (index == combinationSize) {
			result.add(new ArrayList<>(data));
			return;
		}
		for (int i = start; i <= end && end - i + 1 >= combinationSize - index; i++) {
			data.set(index, list.get(i));
			privExecute(data, i + 1, end, index + 1);
		}
	}
	
	List<List<T>> getResult() {
		return result;
	}
}
