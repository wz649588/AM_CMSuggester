package org.eclipse.jdt.internal.compiler.ast;

public class InternalASTNodeFixer {

	// This code is not used for now, but the concept may be used later.
	public void fixCatchBlock(TryStatement tryStatement) {
		if (tryStatement.catchExits == null) {
			int catchCount;
			tryStatement.catchExits = new boolean[catchCount = tryStatement.catchBlocks.length];
			tryStatement.catchExitInitStateIndexes = new int[catchCount];
			for (int i = 0; i < catchCount; i++) {
				tryStatement.catchExits[i] = false;
				tryStatement.catchExitInitStateIndexes[i] = 1;
			}
			tryStatement.mergedInitStateIndex = 0;
			tryStatement.preTryInitStateIndex = 0;
		}

	}

}
