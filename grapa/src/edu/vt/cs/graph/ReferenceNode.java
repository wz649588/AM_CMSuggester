package edu.vt.cs.graph;

import com.ibm.wala.types.MemberReference;
import com.ibm.wala.types.TypeReference;

public class ReferenceNode{
	/**
	 * Use it when you don't know the type of ReferenceNode
	 */
	public static final int UNKNOWN = 0;
	
	/**
	 * Change a method body
	 */
	public static final int CM = 1;
	
	/**
	 * Add a method
	 */
	public static final int AM = 2;
	
	/**
	 * Delete a method
	 */
	public static final int DM = 3;
	
	/**
	 * Add a field
	 */
	public static final int AF = 4;
	
	/**
	 * Delete a field
	 */
	public static final int DF = 5;
	
	/**
	 * Changed field
	 */
	public static final int CF = 6;
	
	/**
	 * Added Class
	 */
	public static final int AC = 7;
	
	/**
	 * Deleted Class
	 */
	public static final int DC = 8;
	
	// changed by Ye Wang, 03/08/2018
//	public MemberReference ref;
	/**
	 * ref's type can be MethodReference, FieldReference, or TypeReference
	 */
	public Object ref;
	
	// Added by Ye Wang, since 10/26/2016
	// type of ReferenceNode, e.g. Added Method (AM), Changed Method (CM)
	public int type;
	
	/**
	 * the type will be set to UNKNOWN
	 * @param ref member reference of the node
	 */
	@Deprecated
	public ReferenceNode(MemberReference ref) {
//		this.ref = ref;
		// Modified by Ye Wang, since 10/26/2016
		this(ref, UNKNOWN);
	}
	
	/**
	 * Constructor
	 * @param ref member reference of the node
	 * @param type the type of ReferenceNode, such as ReferenceNode.CM 
	 */
	public ReferenceNode(MemberReference ref, int type) {
		this.ref = ref;
		this.type = type;
	}
	
	public ReferenceNode(TypeReference ref, int type) {
		this.ref = ref;
		this.type = type;
	}
	
	public static String getTypeString(int type) {
		String s;
		switch (type) {
		case 1:
			s = "CM";
			break;
		case 2:
			s = "AM";
			break;
		case 3:
			s = "DM";
			break;
		case 4:
			s = "AF";
			break;
		case 5:
			s = "DF";
			break;
		case 6:
			s = "CF";
			break;
		case 7:
			s = "AC";
			break;
		case 8:
			s = "DC";
			break;
		default:
			s = "UNKNOWN";
			break;
		}
		return s;
	}
	
	
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ref == null) ? 0 : ref.hashCode());
		return result;
	}




	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ReferenceNode other = (ReferenceNode) obj;
		if (ref == null) {
			if (other.ref != null)
				return false;
		} else if (!ref.equals(other.ref))
			return false;
		
		// added by Ye Wang
		if (type != other.type)
			return false;
		
		return true;
	}




	@Override
	public String toString() {
		if (ref instanceof MemberReference)
			return ((MemberReference) ref).getSignature();
		else
			return ((TypeReference) ref).getName().toString();
	}
}
