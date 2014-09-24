/*
 * Copyright (c) 2014, IETR/INSA of Rennes
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright notice,
 *     this list of conditions and the following disclaimer in the documentation
 *     and/or other materials provided with the distribution.
 *   * Neither the name of the IETR/INSA of Rennes nor the names of its
 *     contributors may be used to endorse or promote products derived from this
 *     software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
package net.sf.orcc.ui.refactoring;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sf.orcc.util.FilesManager;
import net.sf.orcc.util.OrccUtil;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.eclipse.text.edits.TextEdit;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

/**
 * 
 * @author Antoine Lorence
 * 
 */
public class ChangesFactory {

	interface Replacement {
		/**
		 * Check if the given text contains the pattern of this Replacement
		 * instance.
		 * 
		 * @param content
		 * @return
		 */
		boolean isAffected(final String content);

		/**
		 * Get the list of ReplaceEdit corresponding to the replacements
		 * represented by this instance.
		 * 
		 * @param content
		 * @return
		 */
		List<ReplaceEdit> getReplacements(final String content);
	}

	class StandardReplacement implements Replacement {
		private String pattern;
		private String replacement;

		public StandardReplacement(String p, String r) {
			pattern = p;
			replacement = r;
		}

		@Override
		public boolean isAffected(final String content) {
			return content.contains(pattern);
		}

		@Override
		public List<ReplaceEdit> getReplacements(final String content) {
			final List<ReplaceEdit> replacements = new ArrayList<ReplaceEdit>();
			int idx = 0;
			while ((idx = content.indexOf(pattern, idx + 1)) != -1) {
				replacements.add(new ReplaceEdit(idx, pattern.length(),
						replacement));
				idx += pattern.length();
			}
			return replacements;
		}
	}

	class RegexpReplacement implements Replacement {
		private Pattern pattern;
		private String replacement;

		public RegexpReplacement(Pattern p, String r) {
			pattern = p;
			replacement = r;
		}

		@Override
		public boolean isAffected(final String content) {
			return pattern.matcher(content).find();
		}

		@Override
		public List<ReplaceEdit> getReplacements(final String content) {
			final List<ReplaceEdit> replacements = new ArrayList<ReplaceEdit>();
			final Matcher matcher = pattern.matcher(content);
			while (matcher.find()) {
				int s = matcher.start();
				int e = matcher.end();
				final String replaced = pattern
						.matcher(content.substring(s, e)).replaceAll(
								replacement);
				replacements.add(new ReplaceEdit(s, e - s, replaced));
			}
			return replacements;
		}
	}

	/**
	 * The list of replacements to apply, indexed by the suffix of the files
	 * whose can be affected by these replacements
	 */
	final private Multimap<String, Replacement> replacements;
	final private Map<IFile, TextEdit> results;

	public ChangesFactory() {
		replacements = HashMultimap.create();
		results = new HashMap<IFile, TextEdit>();
	}

	public void addReplacement(final String suffix, final Pattern pattern,
			final String replacement) {
		replacements.put(suffix, new RegexpReplacement(pattern, replacement));
	}

	public void addReplacement(final String suffix, final String pattern,
			final String replacement) {
		replacements.put(suffix, new StandardReplacement(pattern, replacement));
	}

	public Change getUniqueFileReplacement(final String title,
			final IFile file, final Pattern pattern, final String repl) {
		final Replacement replacement = new RegexpReplacement(pattern, repl);
		final String content = FilesManager.readFile(file.getRawLocation().toString());
		final MultiTextEdit edits = new MultiTextEdit();
		if(replacement.isAffected(content)) {
			for(ReplaceEdit edit : replacement.getReplacements(content)) {
				edits.addChild(edit);
			}
		}

		final TextFileChange result = new TextFileChange(title, file);
		result.setEdit(edits);
		return result;
	}

	public void clearConfiguration() {
		replacements.clear();
		results.clear();
	}

	/**
	 * Check if the given file will be affected by the current replacements configured.
	 * 
	 * @param file
	 * @return
	 */
	public boolean isAffected(final IFile file) {
		for (Entry<String, Replacement> entry : replacements.entries()) {
			if(entry.getKey().equals(file.getFileExtension())) {
				final Replacement replace = entry.getValue();
				if(replace.isAffected(FilesManager.readFile(file.getRawLocation().toString()))) {
					return true;
				}
			}
		}
		return false;
	}

	public Change getAllChanges(final IProject project, final String title) {
		return getAllChanges(project, title, Collections.<IFile>emptyList());
	}

	/**
	 * Create a CompositeChange containing all replace edits to apply in the
	 * given folder and depending ones.
	 * 
	 * @param project
	 * @param title
	 * @param ignoreList
	 * @return
	 */
	public Change getAllChanges(final IProject project, final String title,
			final Collection<IFile> ignoreList) {
		final List<IFolder> folders = OrccUtil
				.getAllDependingSourceFolders(project);
		List<IFile> files;
		for (String suffix : replacements.keySet()) {
			files = OrccUtil.getAllFiles(suffix, folders);
			files.removeAll(ignoreList);
			for (IFile file : files) {
				computeResults(file, replacements.get(suffix));
			}
		}
		return getFinalresult(title);
	}

	/**
	 * Return the existing TextEdit associated with the given file, creates it
	 * if necessary.
	 * 
	 * @param file
	 * @return
	 */
	private TextEdit getTextEdit(final IFile file) {
		TextEdit textEdit = results.get(file);
		if (textEdit == null) {
			textEdit = new MultiTextEdit();
			results.put(file, textEdit);
		}
		return textEdit;
	}

	private void computeResults(final IFile file,
			final Collection<Replacement> replacements) {
		if (!file.exists()) {
			return;
		}
		final String content = FilesManager.readFile(file.getRawLocation()
				.toString());
		for (Replacement replaceInfo : replacements) {
			if (replaceInfo.isAffected(content)) {
				TextEdit textEdit = getTextEdit(file);
				for (ReplaceEdit replaceEdit : replaceInfo
						.getReplacements(content)) {
					textEdit.addChild(replaceEdit);
				}
			}
		}
	}

	private Change getFinalresult(final String title) {
		final CompositeChange result = new CompositeChange(title);
		for (Entry<IFile, TextEdit> entry : results.entrySet()) {
			final IFile file = entry.getKey();
			final TextFileChange fileChange = new TextFileChange("Changes to "
					+ file.getName(), file);
			fileChange.setEdit(entry.getValue());
			result.add(fileChange);
		}
		return result.getChildren().length > 0 ? result : null;
	}
}
