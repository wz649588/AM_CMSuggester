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
package ca.mcgill.cs.swevo.ppa.ui;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class PPAMainPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public PPAMainPreferencePage() {
		super(GRID);
		setPreferenceStore(PPAUIActivator.getDefault().getPreferenceStore());
		setDescription("PPA Preferences");
	}

	@Override
	protected void createFieldEditors() {
		addField(new StringFieldEditor(PPAPreferenceConstants.PPA_PROJECT_PREF,"PPA Internal Project",getFieldEditorParent()));
		addField(new IntegerFieldEditor(PPAPreferenceConstants.PPA_MAX_REQUESTS,"Max Number of Concurrent Requests\n(requires restart)",getFieldEditorParent()));
	}

	public void init(IWorkbench workbench) {
	}

}
