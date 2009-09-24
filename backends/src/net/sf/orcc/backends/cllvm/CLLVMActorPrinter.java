/*
 * Copyright (c) 2009, IETR/INSA of Rennes
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
package net.sf.orcc.backends.cllvm;

import java.io.IOException;

import net.sf.orcc.backends.PluginGroupLoader;
import net.sf.orcc.backends.c.ConstPrinter;
import net.sf.orcc.backends.c.ExprToString;
import net.sf.orcc.backends.c.TypeToString;
import net.sf.orcc.backends.c.VarDefPrinter;
import net.sf.orcc.backends.multicore.MultiCoreActorPrinter;

/**
 * LLVM Actor printer.
 * 
 * @author J�r�me GORIN
 * 
 */
public class CLLVMActorPrinter extends MultiCoreActorPrinter {


	/**
	 * Creates a new network printer with the template "C.st".
	 * 
	 * @throws IOException
	 *             If the template file could not be read.
	 */
	public CLLVMActorPrinter() throws IOException {
		this("C_actor");

		constPrinter = new ConstPrinter(group);
		typePrinter = new TypeToString();
		varDefPrinter = new VarDefPrinter(typePrinter);
		exprPrinter = new ExprToString(varDefPrinter);
	}

	/**
	 * Creates a new network printer using the given template file name.
	 * 
	 * @param name
	 *            The template file name.
	 * @throws IOException
	 *             If the template file could not be read.
	 */
	protected CLLVMActorPrinter(String name) throws IOException {
		group = new PluginGroupLoader().loadGroup(name);
	}
}
