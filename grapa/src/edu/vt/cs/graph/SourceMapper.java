package edu.vt.cs.graph;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.SourceRange;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAConversionInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;

public class SourceMapper {

	Map<String, CompilationUnit> typeToCu = null;
	Map<CompilationUnit, LineMapper> lineMappers = null;
	
	public SourceMapper() {
		typeToCu = new HashMap<String, CompilationUnit>();
		lineMappers = new HashMap<CompilationUnit, LineMapper>();
	}
	
	public void add(ASTNode ast) {
		if (lineMappers.containsKey(ast))
			return;
		CompilationUnit cu = (CompilationUnit)ast;
		ASTNodeCollector collector = new ASTNodeCollector(cu);
		Map<Integer, List<ASTNode>> lineToAsts = collector.getLineToAsts();
		Map<MethodDeclaration, SourceRange> methodToRange = collector.getMethodToRange();
		LineMapper mapper = new LineMapper(lineToAsts, methodToRange);
		Set<String> types = collector.getTypes();
		lineMappers.put(cu, mapper);
		for (String t : types) {
			typeToCu.put(t, cu);
		}
	}

	public CompilationUnit findCu(StatementWithInstructionIndex s, CompilationUnit defaultCu) {
		CompilationUnit cu = defaultCu;
		SSAInstruction instr = s.getInstruction();
		if (instr instanceof SSAFieldAccessInstruction) {
			SSAFieldAccessInstruction sInstr = (SSAFieldAccessInstruction)instr;
			String typeName = TypeNameConverter.binaryToQualified(sInstr.getDeclaredField().getDeclaringClass().getName().toString());
			cu = typeToCu.get(typeName);			
		}
		return cu;
	}
	
	public CompilationUnit getCu(String typeName) {
		return typeToCu.get(typeName);
	}
	
	public LineMapper getLineMapper(CompilationUnit cu) {
		if (!lineMappers.containsKey(cu)) {
			add(cu);
		}
		return lineMappers.get(cu);
	}
}
