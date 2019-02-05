package edu.vt.cs.changes;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.NodeFinder;

import com.ibm.wala.ide.util.ASTNodeFinder;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.util.collections.Pair;

import edu.vt.cs.changes.api.FieldAPIResolver;
import edu.vt.cs.changes.api.MethodAPIResolver;
import edu.vt.cs.changes.api.TypeAPIResolver;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import partial.code.grapa.commit.CommitComparator;
import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import partial.code.grapa.mapping.ClientMethod;

public class MigrationChangeDetector {

	public static final String libStr = "org.apache.lucene";
	
	private DataFlowAnalysisEngine leftEngine = null;
	private DataFlowAnalysisEngine rightEngine = null;
	private List<ChangeFact> cfList;
	
	private void analyzeChanges(Map<IBinding, Set<ChangeFact>> oldbindings, Map<IBinding, Set<ChangeFact>> newbindings) {
		IBinding b = null;
		IBinding missing = null;
		Map<IMethodBinding, Set<ChangeFact>> missingMethods = new HashMap<IMethodBinding, Set<ChangeFact>>();
		Map<IVariableBinding, Set<ChangeFact>> missingFields = new HashMap<IVariableBinding, Set<ChangeFact>>();
		Map<ITypeBinding, Set<ChangeFact>> missingTypes = new HashMap<ITypeBinding, Set<ChangeFact>>();
		Set<ChangeFact> value = null;
		for (Entry<IBinding, Set<ChangeFact>> entry : oldbindings.entrySet()) {
			b = entry.getKey();
			value = entry.getValue();
			missing = rightEngine.lookupBinding(b);
			if (missing == null) {
				continue;
			}
			if (b instanceof IMethodBinding) {
				if (missing.equals(b)) {
					missingMethods.put((IMethodBinding)b, value);
				} else {
					missingTypes.put((ITypeBinding)missing, value);
				}
			} else if (b instanceof IVariableBinding) {
				if (missing.equals(b)) {
					missingFields.put((IVariableBinding)b, value);
				} else {
					missingFields.put((IVariableBinding)missing, value);
				}
			}
		}
		new MethodAPIResolver(leftEngine, rightEngine).resolve(missingMethods);
//		MethodAPIResolver.resolve(missingMethods, leftEngine, rightEngine);
//		FieldAPIResolver.resolve(missingFields, leftEngine, rightEngine);
//		TypeAPIResolver.resolve(missingTypes, leftEngine, rightEngine);
	}
	
	public void detect(List<ChangeFact> cfList, CommitComparator comparator) {
		leftEngine = comparator.getLeftAnalysisEngine();
		rightEngine = comparator.getRightAnalysisEngine();
	
		this.cfList = cfList;
		Map<IBinding, Set<ChangeFact>> oldBindings = new HashMap<IBinding, Set<ChangeFact>>();
		Map<IBinding, Set<ChangeFact>> newBindings = new HashMap<IBinding, Set<ChangeFact>>();
		Set<ChangeFact> cfSet = null;
		for (ChangeFact cf: cfList) {
			for (ChangeMethodData c : cf.changedMethodData) {				
				Map<IBinding, Set<SourceCodeRange>> oldmap = parseAPIs(leftEngine, libStr, c.oldMethod, c.oldASTRanges);
				Map<IBinding, Set<SourceCodeRange>> newmap = parseAPIs(rightEngine, libStr, c.newMethod, c.newASTRanges);							
				Set<IBinding> common = new HashSet<IBinding>(oldmap.keySet());
				common.retainAll(newmap.keySet());
				if (!common.isEmpty()) {
					for (IBinding key : common) {
						oldmap.remove(key);
						newmap.remove(key);
					}
				}
				c.oldBindingMap = oldmap;
				c.newBindingMap = newmap;
				for (IBinding key : oldmap.keySet()) {
					cfSet = oldBindings.get(key);
					if (cfSet == null) {
						cfSet = new HashSet<ChangeFact>();
						oldBindings.put(key, cfSet);
					}
					cfSet.add(cf);
				}
				for (IBinding key : newmap.keySet()) {
					cfSet = newBindings.get(key);
					if (cfSet == null) {
						cfSet = new HashSet<ChangeFact>();
						newBindings.put(key, cfSet);
					}
					cfSet.add(cf);
				}
			}
		}	
		analyzeChanges(oldBindings, newBindings);
	}
	
	private Map<IBinding, Set<SourceCodeRange>> parseAPIs(DataFlowAnalysisEngine engine,
			String libStr, ClientMethod m, List<SourceCodeRange> ranges) {
		MethodDeclaration md = m.methodbody;
		ASTNode n = null;
		LibAPIParser parser = new LibAPIParser(engine, libStr);
		Map<IBinding, Set<SourceCodeRange>> bindings = new HashMap<IBinding, Set<SourceCodeRange>>();
		List<IBinding> bindingList  = null;
		Set<SourceCodeRange> value = null;
		for (SourceCodeRange r : ranges) {
			n = NodeFinder.perform(md, r.startPosition, r.length);
			parser.init();
			n.accept(parser);
			bindingList = parser.getBindings();
			for (IBinding b : bindingList) {
				value = bindings.get(b);
				if (value == null) {
					value = new HashSet<SourceCodeRange>();
					bindings.put(b, value);
				}				
				value.add(r);				
			}			
		}
		return bindings;
	}
}
