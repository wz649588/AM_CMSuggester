package edu.vt.cs.prediction.neo;

import java.util.Comparator;
import java.util.PriorityQueue;

public class Temp {

	public static void main(String[] args) {
		Comparator<Integer> comparator = new Comparator<Integer>() {

			@Override
			public int compare(Integer o1, Integer o2) {
				return o2 - o1;
			}
			
		};
		PriorityQueue<Integer> queue = new PriorityQueue<>(3, comparator);
		queue.add(4);
		queue.add(6);
		queue.add(2);
		while (!queue.isEmpty()) {
			System.out.println(queue.poll());
		}
	}
}
