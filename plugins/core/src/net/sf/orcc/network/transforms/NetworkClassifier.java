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
package net.sf.orcc.network.transforms;

import net.sf.orcc.OrccException;
import net.sf.orcc.ir.Actor;
import net.sf.orcc.ir.ActorClass;
import net.sf.orcc.ir.ActorTransformation;
import net.sf.orcc.ir.classes.StaticClass;
import net.sf.orcc.ir.transforms.DeadGlobalElimination;
import net.sf.orcc.ir.transforms.PhiRemoval;
import net.sf.orcc.network.Network;
import net.sf.orcc.network.NetworkClass;
import net.sf.orcc.network.classes.CSDFNetworkClass;
import net.sf.orcc.network.classes.DynamicNetworkClass;
import net.sf.orcc.network.classes.SDFNetworkClass;
import net.sf.orcc.tools.classifier.ActorClassifierIndependent;

/**
 * This class defines a network transformation that classifies all actors using
 * the {@link ActorClassifierIndependent} class.
 * 
 * @author Matthieu Wipliez
 * 
 */
public class NetworkClassifier implements INetworkTransformation {

	private static int SDF = 0;
	private static int CSDF = 1;
	private static int DYNAMIC = 2;

	/**
	 * Creates a new classifier
	 */

	public NetworkClassifier() {
	}

	@Override
	public void transform(Network network) throws OrccException {
		// will remove phi so the actor can be interpreted
		ActorTransformation phi = new PhiRemoval();

		// will remove dead globals (they are useless anyway)
		ActorTransformation dge = new DeadGlobalElimination();

		for (Actor actor : network.getActors()) {
			dge.transform(actor);
			phi.transform(actor);

			ActorClassifierIndependent classifier = new ActorClassifierIndependent();
			ActorClass clasz = classifier.classify(actor);
			actor.setActorClass(clasz);
		}

		network.setNetworkClass(getNetworkClass(network));
	}

	private NetworkClass getNetworkClass(Network network) {
		NetworkClass networkClass = new SDFNetworkClass();

		int status = SDF;

		for (Actor actor : network.getActors()) {
			ActorClass clasz = actor.getActorClass();

			if (clasz.isDynamic()) {
				if (status < DYNAMIC) {
					networkClass = new DynamicNetworkClass();
					status = DYNAMIC;
				}
			} else if (clasz.isStatic()) {
				if (status < CSDF) {
					StaticClass staticClass = (StaticClass) clasz;
					if (staticClass.getNumberOfPhases() > 1) {
						networkClass = new CSDFNetworkClass();
						status = CSDF;
					}
				}
			}
		}
		return networkClass;

	}
}
