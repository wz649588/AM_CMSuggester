/*******************************************************************************
 * PPA - Partial Program Analysis for Java
 * Copyright (C) 2008 Barthelemy Dagenais
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either 
 * version 3 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this library. If not, see 
 * <http://www.gnu.org/licenses/lgpl-3.0.txt>
 *******************************************************************************/
package ca.mcgill.cs.swevo.ppa;

public class PPAOptions {

	private boolean allowMemberInference = true;

	private boolean allowCollectiveMode = false;

	private boolean allowTypeInferenceMode = true;

	private boolean allowMethodBindingMode = true;

	private int maxMISize = -1;

	private boolean allowAnalyzeProject = false;
	
	public PPAOptions() {
		super();
	}

	public PPAOptions(boolean allowMemberInference, boolean allowCollectiveMode,
			boolean allowTypeInferenceMode, boolean allowMethodBindingMode, int maxMISize) {
		super();
		this.allowMemberInference = allowMemberInference;
		this.allowCollectiveMode = allowCollectiveMode;
		this.allowTypeInferenceMode = allowTypeInferenceMode;
		this.allowMethodBindingMode = allowMethodBindingMode;
		this.maxMISize = maxMISize;
	}

	public boolean isAllowAnalyzeProject() {
		return allowAnalyzeProject;
	}

	public int getMaxMISize() {
		return maxMISize;
	}

	public boolean isAllowCollectiveMode() {
		return allowCollectiveMode;
	}

	public boolean isAllowMemberInference() {
		return allowMemberInference;
	}

	public boolean isAllowMethodBindingMode() {
		return allowMethodBindingMode;
	}

	public boolean isAllowTypeInferenceMode() {
		return allowTypeInferenceMode;
	}

	public void setAllowCollectiveMode(boolean allowCollectiveMode) {
		this.allowCollectiveMode = allowCollectiveMode;
	}

	public void setAllowMemberInference(boolean allowMemberInference) {
		this.allowMemberInference = allowMemberInference;
	}

	public void setAllowMethodBindingMode(boolean allowMethodBindingMode) {
		this.allowMethodBindingMode = allowMethodBindingMode;
	}

	public void setAllowTypeInferenceMode(boolean allowTypeInferenceMode) {
		this.allowTypeInferenceMode = allowTypeInferenceMode;
	}

	public void setMaxMISize(int maxMISize) {
		this.maxMISize = maxMISize;
	}

	public void setAllowAnalyzeProject(boolean b) {
		// TODO Auto-generated method stub
		allowAnalyzeProject  = b;
	}
	
	

}
