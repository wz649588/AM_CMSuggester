package edu.vt.cs.prediction;

import java.util.ArrayList;
import java.util.List;

public class Chunk {
	private List<ChunkMolecule> moles;
	
	private MoleculeNum num;
	
	public Chunk(String word) {
		moles = new ArrayList<ChunkMolecule>();
		ChunkMolecule mole = new ChunkMolecule(word);
		moles.add(mole);
		num = new MoleculeNum(MoleculeNumType.FIXED, 1);
	}
	
	private class MoleculeNum {
		private MoleculeNumType type;
		private int num;
		
		MoleculeNum(MoleculeNumType type) {
			this.type = type;
		}
		
		MoleculeNum(MoleculeNumType type, int num) {
			this.type = type;
			this.num = num;
		}
	}

	private enum MoleculeNumType {
		FIXED,
		ZERO_PLUS,
		ONE_PLUS
	}
}

