package edu.vt.cs.diffparser.textdiff;

public class UpdatedFileRecord extends FileRecord {

	String newFileName;

	public UpdatedFileRecord(String f, String f2) {
		super(f);
		newFileName = f2;
	}
}
