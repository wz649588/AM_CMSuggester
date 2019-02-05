package edu.vt.cs.prediction;

import java.util.ArrayList;
import java.util.List;

public class ChunkList {
	private List<Chunk> chunks;
	
	/**
	 * Original pieces of a variable name
	 */
	private List<String> original;
	
	public ChunkList(List<String> words) {
		this.original = words;
		chunks = new ArrayList<Chunk>();
		for (String w: words) {
			Chunk chunk = new Chunk(w);
			chunks.add(chunk);
		}
	}
	
	public List<Chunk> getChunks() {
		return chunks;
	}
}
