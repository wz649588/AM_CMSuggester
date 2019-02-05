package edu.vt.cs.prediction.ml;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;

/**
 * Given the WALA IR of a method, this class can extract various information
 * of the method.
 * @author Ye Wang
 * @since 04/30/2017
 *
 */
public class MethodAnalyzer {
	
	/**
	 * WALA IR of the method
	 */
	private IR ir;

	public MethodAnalyzer(IR ir) {
		this.ir = ir;
	}
	
	/**
	 * Get the names of fields used in the method, a name may appear more than once.
	 * @return field name list
	 */
	public List<String> getFieldNameList() {
		if (ir == null)
			return Collections.emptyList();
		
		List<String> fieldNames = new ArrayList<>();
		for (SSAInstruction instr: ir.getInstructions()) {
			if (instr instanceof SSAFieldAccessInstruction) {
				SSAFieldAccessInstruction fInstr = (SSAFieldAccessInstruction)instr;
				FieldReference fieldRef = fInstr.getDeclaredField();
				String fieldName = fieldRef.getName().toString();
				fieldNames.add(fieldName);
			}
		}
		return fieldNames;
	}
	
	/**
	 * Get the names of local variables in the method. A name may appear more than once.
	 * @return local variable name list
	 */
	public List<String> getLocalNameList() {
		if (ir == null)
			return Collections.emptyList();
		
		String[][] valueNumberNames = null;
		try {
			Object localMap = this.getPrivateFieldValue(ir, "localMap");
			Object dontKnowWhatItIs = this.getPrivateFieldValue(localMap, "this$0");
			Object debugInfo = this.getPrivateFieldValueInSuperClass(dontKnowWhatItIs, "debugInfo");
			valueNumberNames = (String[][])this.getPrivateFieldValue(debugInfo, "valueNumberNames");
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		}
		List<String> localVars = new ArrayList<>();
		// check if the method is a static method
		if (valueNumberNames.length >= 2 && valueNumberNames[1].length == 1 && !valueNumberNames[1][0].equals("this")) {
			localVars.add(valueNumberNames[1][0]);
		}
		for (int i = 2; i < valueNumberNames.length; i++) {
			if (valueNumberNames[i].length == 1)
				localVars.add(valueNumberNames[i][0]);
		}
		
		return localVars;
	}
	
	public List<String> getMethodNameList() {
		if (ir == null)
			return Collections.emptyList();
		
		List<String> methodNames = new ArrayList<>();
		for (SSAInstruction instr: ir.getInstructions()) {
			if (instr == null)
				continue;
			if (instr instanceof SSAAbstractInvokeInstruction) {
				MethodReference mRef = ((SSAAbstractInvokeInstruction)instr).getDeclaredTarget();
				String methodName = mRef.getName().toString();
				methodNames.add(methodName);
			}
		}
		
		return methodNames;
	}
	
	// This is a helper method
	private Object getPrivateFieldValue(Object c, String fieldName) throws NoSuchFieldException {
		Class<?> klass = c.getClass();
		Field field = null;
		try {
			field = klass.getDeclaredField(fieldName);
		} catch (SecurityException e) {
			e.printStackTrace();
		}
		
		field.setAccessible(true);
		Object fieldObject = null;
		try {
			fieldObject = field.get(c);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			e.printStackTrace();
		}
		
		return fieldObject;
	}
	
	// This is a helper method.
	private Object getPrivateFieldValueInSuperClass(Object c, String fieldName) throws NoSuchFieldException {
		Class<?> klass = c.getClass();
		Class<?> superClass = (Class<?>) klass.getGenericSuperclass();
		Field field = null;
		try {
			field = superClass.getDeclaredField(fieldName);
		} catch (SecurityException e) {
			e.printStackTrace();
		}
		
		field.setAccessible(true);
		Object fieldObject = null;
		try {
			fieldObject = field.get(c);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			e.printStackTrace();
		}
		return fieldObject;
	}
}
