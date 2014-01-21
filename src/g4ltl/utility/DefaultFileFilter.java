/* G4LTL: Games for LTL Synthesis
 *
 * Copyright (c) 2013, Chih-Hong Cheng, 
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of the <organization> nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL Chih-Hong Cheng BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package g4ltl.utility;


import java.io.File;
import javax.swing.JFileChooser;
import javax.swing.filechooser.FileFilter;

/**
 * Filter for use in a {@link JFileChooser}.
 * 
 * @author Chihhong Cheng
 * @version 0.2 2012/08/08
 */ 
public class DefaultFileFilter extends FileFilter
{

	/**
	 * Extension of accepted files.
	 */
	protected String ext;

	/**
	 * Description of accepted files.
	 */
	protected String desc;

	/**
	 * Constructs a new filter for the specified extension and descpription.
	 * 
	 * @param extension
	 *            The extension to accept files with.
	 * @param description
	 *            The description of the file format.
	 */
	public DefaultFileFilter(String extension, String description)
	{
		ext = extension.toLowerCase();
		desc = description;
	}

	/**
	 * Returns true if <code>file</code> is a directory or ends with
	 * {@link #ext}.
	 * 
	 * @param file
	 *            The file to be checked.
	 * @return Returns true if the file is accepted.
	 */
	public boolean accept(File file)
	{
		return file.isDirectory() || file.getName().toLowerCase().endsWith(ext);
	}

	/**
	 * Returns the description for accepted files.
	 * 
	 * @return Returns the description.
	 */
	public String getDescription()
	{
		return desc;
	}

	/**
	 * Returns the extension for accepted files.
	 * 
	 * @return Returns the extension.
	 */
	public String getExtension()
	{
		return ext;
	}

	/**
	 * Sets the extension for accepted files.
	 * 
	 * @param extension
	 *            The extension to set.
	 */
	public void setExtension(String extension)
	{
		this.ext = extension;
	}

	

}
