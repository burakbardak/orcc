/*
 * Copyright (c) 2009-2010, IETR/INSA of Rennes
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
package net.sf.orcc.backends;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import net.sf.orcc.network.Network;

import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.StringTemplateGroup;

/**
 * This class defines a C network printer.
 * 
 * @author Matthieu Wipliez
 * 
 */
public class NetworkPrinter {

	private StringTemplateGroup group;

	/**
	 * Creates a new network printer using the given template file name.
	 * 
	 * @param name
	 *            The template file name.
	 * @throws IOException
	 *             If the template file could not be read.
	 */
	public NetworkPrinter(String name) throws IOException {
		group = new TemplateGroupLoader().loadGroup(name);
	}

	/**
	 * Prints the given network to a file whose name is given. debugFifos
	 * specifies whether debug information should be printed about FIFOs, and
	 * fifoSize is the default FIFO size.
	 * 
	 * @param fileName
	 *            The output file name.
	 * @param network
	 *            The network to generate code for.
	 * @param debugFifos
	 *            Whether debug information should be printed about FIFOs.
	 * @param fifoSize
	 *            Default FIFO size.
	 * @throws IOException
	 *             if there is an I/O error
	 */
	public void printNetwork(String fileName, Network network,
			boolean debugFifos, int fifoSize) throws IOException {
		StringTemplate template = group.getInstanceOf("network");

		network.computeGraphMaps();

		template.setAttribute("debugFifos", debugFifos);
		template.setAttribute("network", network);
		template.setAttribute("fifoSize", fifoSize);

		byte[] b = template.toString(80).getBytes();
		OutputStream os = new FileOutputStream(fileName);
		os.write(b);
		os.close();
	}

}
