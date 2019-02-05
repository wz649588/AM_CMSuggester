package edu.vt.cs.changes.api;

import com.ibm.wala.util.debug.Assertions;

public class InstType {
	public static final int EXCEPTION = -1; // this is used to mark an exception data node
	public static final int IGNORE = 0;
	public static final int INVOKE = 1;
	public static final int GET_STATIC = 2;
	public static final int GET = 3;
	public static final int NEW = 4;
	public static final int CAST = 5;
	public static final int ASTORE = 6;
	public static final int BRANCH = 7;
	public static final int GOTO = 8;
	public static final int BINOP = 9;
	public static final int UNARYOP = 10;
	public static final int THROW = 11;
	public static final int RETURN = 12;
	public static final int LOAD_META = 13;
	public static final int MONITOR = 14;
	
	public static String toTypeString(int iType) {
		switch(iType) {
		case InstType.ASTORE:
			return "Astore";
		case InstType.BINOP:
			return "Binop";
		case InstType.BRANCH:
			return "Branch";
		case InstType.CAST:
			return "Cast";
		case InstType.GET:
			return "Get";
		case InstType.GET_STATIC:
			return "Get static";
		case InstType.GOTO:
			return "Goto";
		case InstType.INVOKE:
			return "Invoke";
		case InstType.LOAD_META:
			return "Load Metadata";
		case InstType.MONITOR:
			return "Monitor";
		case InstType.NEW:
			return "New";
		case InstType.RETURN:
			return "Return";
		case InstType.THROW:
			return "Throw";
		case InstType.UNARYOP:
			return "UnaryOp";
		default:
			Assertions.UNREACHABLE("Need more process for type " + iType );
			return "";
		}
	}

}
