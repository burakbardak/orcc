/*
 * Copyright (c) 2010, IRISA
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
 *   * Neither the name of the IRISA nor the names of its
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
package net.sf.orcc.backends.transformations;

import net.sf.orcc.ir.Expression;
import net.sf.orcc.ir.Instruction;
import net.sf.orcc.ir.expr.VarExpr;
import net.sf.orcc.ir.instructions.Load;
import net.sf.orcc.ir.instructions.Read;
import net.sf.orcc.ir.instructions.Store;
import net.sf.orcc.ir.instructions.Write;
import net.sf.orcc.ir.transformations.AbstractActorTransformation;

/**
 * This class defines an actor transformation that replace list of one element
 * used in write/read instructions by a scalar
 * 
 * @author Herve Yviquel
 * 
 */
public class ListOfOneElementToScalarTransformation extends
		AbstractActorTransformation {

	@Override
	public void visit(Read read) {
		if (read.getNumTokens() == 1 && instructionIterator.hasNext()) {
			Instruction instruction = instructionIterator.next();
			if (instruction.isLoad()) {
				Load load = (Load) instruction;
				read.setTarget(load.getTarget());
				instructionIterator.remove();
			}
		}
	}

	@Override
	public void visit(Write write) {
		if (write.getNumTokens() == 1 && instructionIterator.hasPrevious()) {
			instructionIterator.previous();
			if (instructionIterator.hasPrevious()) {
				Instruction instruction = instructionIterator.previous();
				if (instruction.isStore()) {
					Store store = (Store) instruction;
					Expression expr = store.getValue();
					if (expr.isVarExpr()) {
						VarExpr var = (VarExpr) expr;
						write.setTarget(var.getVar().getVariable());
						instructionIterator.remove();
					}
				}
				instructionIterator.next();
			}
			instructionIterator.next();
		}
	}

}
