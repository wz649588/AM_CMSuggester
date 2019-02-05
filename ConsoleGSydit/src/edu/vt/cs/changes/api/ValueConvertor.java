package edu.vt.cs.changes.api;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.Value;

public class ValueConvertor {

	SymbolTable st = null;
	IR ir = null;
	public ValueConvertor(IR ir) {
		this.st = ir.getSymbolTable();
		this.ir = ir;
	}
	
	public String convert(int index, int vn) {
		
		String[] names = null;
		try {
			names = ir.getLocalNames(index, vn);
		} catch(Exception e) {
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
		String str = null;
		if (names.length == 0) {
			str = "v" + vn;
		} else if (names.length == 1){
			str = names[0];
		} else {
			System.err.println("Need more process");
		}
		return str;
	}
}
