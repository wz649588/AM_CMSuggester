package edu.vt.cs.diffparser.astdiff.edits;

import java.io.Serializable;

import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.CONTENT_TYPE;

public interface ITreeEditOperation<T> extends Serializable{

	public static enum EDIT {
		EDIT_GROUP,
		INSERT,
		DELETE,
		UPDATE,
		MOVE,
	};
	
	public static enum CONTENT_TYPE {
		PACKAGE,
		IMPORT,
		INTERFACE,
		SUPER,
		TYPE_DECLARATION,
		FIELD_DECLARATION,
		METHOD_DECLARATION,
		METHOD_NAME,
		PARAMETER,
		PARAMETER_NAME,
		PARAMETER_TYPE,
		COMPILATION_UNIT,
		DECLARATION,
		STATEMENT
	};
	
	public EDIT getOperationType();
		
	public CONTENT_TYPE getContentType();
}
