package edu.vt.cs.prediction;

public class ChunkMolecule {
	private ChunkAtom atom;
	
	private String content; 
	
	public ChunkMolecule(String word) {
		content = word;
		if (Character.isDigit(word.charAt(0))) {
			atom = ChunkAtom.NUMBER;
		} else if (Character.isLowerCase(word.charAt(0))){
			atom = ChunkAtom.LOWER;
		} else if (word.length() > 1 && Character.isLowerCase(word.charAt(1))) { // "Name"
			atom = ChunkAtom.CAPITAL;
		} else { // "NAME"
			atom = ChunkAtom.UPPER;
		}
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (!(obj instanceof ChunkMolecule))
			return false;
		
		ChunkMolecule m = (ChunkMolecule)obj;
		if (this.atom != m.atom)
			return false;
		else if (this.atom != ChunkAtom.DEFINITE)
			return true;
		else if (this.content.equals(m.content))
			return true;
		
		return false;
	}
}