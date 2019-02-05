package edu.vt.cs.diffparser.util;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;

public class CollectionUtil<T> {

	public List<T> convertToList(Enumeration<T> enumeration) {
		List<T> list = new ArrayList<T>();
		while (enumeration.hasMoreElements()) {
			list.add(enumeration.nextElement());
		}
		return list;
	}
}
