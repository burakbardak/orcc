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
package net.sf.orcc.ir.transformations;

import org.eclipse.emf.ecore.util.EcoreUtil;

import net.sf.orcc.ir.NodeBlock;
import net.sf.orcc.ir.NodeIf;
import net.sf.orcc.ir.NodeWhile;
import net.sf.orcc.ir.Procedure;
import net.sf.orcc.ir.util.AbstractActorVisitor;

/**
 * This class defines an actor transformation that combines blocks of
 * instructions together.
 * 
 * @author Matthieu Wipliez
 * 
 */
public class BlockCombine extends AbstractActorVisitor<Object> {

	private NodeBlock previous;

	@Override
	public Object caseNodeBlock(NodeBlock block) {
		if (previous == null) {
			previous = block;
		} else {
			// add instructions of this block after previous block's
			// instructions
			previous.getInstructions().addAll(block.getInstructions());

			// remove this block
			EcoreUtil.remove(block);
			indexNode--;
		}

		return null;
	}

	@Override
	public Object caseNodeIf(NodeIf node) {
		// so that previous blocks are not linked to then branch
		previous = null;
		doSwitch(node.getThenNodes());

		// so that previous blocks are not linked to else branch
		previous = null;
		doSwitch(node.getElseNodes());

		// so that neither then nor else branch are linked to this join
		// as a matter of fact, this also ensures correctness in nested ifs
		previous = null;
		doSwitch(node.getJoinNode());

		// we do not set previous to null again, because join may be combined
		// with next blocks (actually it needs to be).

		return null;
	}

	@Override
	public Object caseProcedure(Procedure procedure) {
		previous = null;
		return super.caseProcedure(procedure);
	}

	@Override
	public Object caseNodeWhile(NodeWhile node) {
		// previous blocks are not linked to the body of the while
		previous = null;
		doSwitch(node.getNodes());

		// no previous block to be linked to
		previous = null;

		return null;
	}

}
