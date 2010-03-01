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
package net.sf.orcc.network;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.orcc.OrccException;
import net.sf.orcc.ir.Actor;
import net.sf.orcc.ir.GlobalVariable;
import net.sf.orcc.ir.Port;
import net.sf.orcc.network.transforms.Instantiator;
import net.sf.orcc.network.transforms.NetworkClassifier;
import net.sf.orcc.network.transforms.NetworkFlattener;
import net.sf.orcc.tools.normalizer.ActorMerger;
import net.sf.orcc.tools.normalizer.ActorNormalizer;
import net.sf.orcc.util.OrderedMap;

import org.jgrapht.DirectedGraph;

/**
 * An XDF network.
 * 
 * @author Matthieu Wipliez
 * 
 */
public class Network {

	private Map<Connection, Integer> connectionMap;

	private DirectedGraph<Vertex, Connection> graph;

	private OrderedMap<Port> inputs;

	private String name;

	private OrderedMap<Port> outputs;

	private OrderedMap<GlobalVariable> parameters;

	private Map<Connection, Vertex> sourceMap;

	private Map<Connection, Vertex> targetMap;

	private OrderedMap<GlobalVariable> variables;

	/**
	 * Creates a new network with the given name, inputs, outputs, and graph.
	 * 
	 * @param name
	 *            network name
	 * @param inputs
	 *            list of input ports
	 * @param outputs
	 *            list of output ports
	 * @param graph
	 *            graph representing the network's contents
	 */
	public Network(String name, OrderedMap<Port> inputs,
			OrderedMap<Port> outputs, OrderedMap<GlobalVariable> parameters,
			OrderedMap<GlobalVariable> variables,
			DirectedGraph<Vertex, Connection> graph) {
		this.name = name;
		this.inputs = inputs;
		this.outputs = outputs;
		this.parameters = parameters;
		this.variables = variables;
		this.graph = graph;
	}

	/**
	 * Classifies all actors of this network.
	 * 
	 * @throws OrccException
	 *             if something goes wrong
	 */
	public void classifyActors() throws OrccException {
		new NetworkClassifier().transform(this);
	}

	/**
	 * Computes the source map and target maps that associate each connection to
	 * its source vertex (respectively target vertex).
	 */
	public void computeGraphMaps() {
		sourceMap = new HashMap<Connection, Vertex>();
		for (Connection connection : graph.edgeSet()) {
			sourceMap.put(connection, graph.getEdgeSource(connection));
		}

		targetMap = new HashMap<Connection, Vertex>();
		for (Connection connection : graph.edgeSet()) {
			targetMap.put(connection, graph.getEdgeTarget(connection));
		}

		connectionMap = new HashMap<Connection, Integer>();
		int i = 0;
		for (Connection connection : graph.edgeSet()) {
			connectionMap.put(connection, i++);
		}
	}

	/**
	 * Flattens this network.
	 * 
	 * @throws OrccException
	 */
	public void flatten() throws OrccException {
		new NetworkFlattener().transform(this);
	}

	/**
	 * Returns the list of actors referenced by the graph of this network.
	 * 
	 * @return a list of actors
	 */
	public List<Actor> getActors() {
		List<Actor> actors = new ArrayList<Actor>();
		for (Vertex vertex : getGraph().vertexSet()) {
			if (vertex.isInstance()) {
				Instance instance = vertex.getInstance();
				if (instance.isActor()) {
					Actor actor = instance.getActor();
					actors.add(actor);
				}
			}
		}

		return actors;
	}

	/**
	 * Returns the list of broadcasts referenced by the graph of this network.
	 * 
	 * @return a list of actors
	 */
	public List<Broadcast> getBroadcasts() {
		List<Broadcast> broadcasts = new ArrayList<Broadcast>();
		for (Vertex vertex : getGraph().vertexSet()) {
			if (vertex.isInstance()) {
				Instance instance = vertex.getInstance();
				if (instance.isBroadcast()) {
					Broadcast bcast = (Broadcast) instance;
					broadcasts.add(bcast);
				}
			}
		}

		return broadcasts;
	}

	/**
	 * Returns a map that associates each connection to a unique integer.
	 * 
	 * @return a map that associates each connection to a unique integer
	 */
	public Map<Connection, Integer> getConnectionMap() {
		return connectionMap;
	}

	/**
	 * Returns the list of this graph's connections.
	 * 
	 * @return the list of this graph's connections
	 */
	public List<Connection> getConnections() {
		return Arrays.asList(graph.edgeSet().toArray(new Connection[0]));
	}

	/**
	 * Returns a graph representing the network's contents
	 * 
	 * @return a graph representing the network's contents
	 */
	public DirectedGraph<Vertex, Connection> getGraph() {
		return graph;
	}

	/**
	 * Returns the list of this network's input ports
	 * 
	 * @return the list of this network's input ports
	 */
	public OrderedMap<Port> getInputs() {
		return inputs;
	}

	/**
	 * Returns the list of instances referenced by the graph of this network.
	 * 
	 * @return a list of instances
	 */
	public List<Instance> getInstances() {
		List<Instance> instances = new ArrayList<Instance>();
		for (Vertex vertex : getGraph().vertexSet()) {
			if (vertex.isInstance()) {
				Instance instance = vertex.getInstance();
				instances.add(instance);
			}
		}

		return instances;
	}

	/**
	 * Returns the name of this network
	 * 
	 * @return the name of this network
	 */
	public String getName() {
		return name;
	}

	/**
	 * Returns the list of this network's output ports
	 * 
	 * @return the list of this network's output ports
	 */
	public OrderedMap<Port> getOutputs() {
		return outputs;
	}

	/**
	 * Returns the list of this network's parameters
	 * 
	 * @return the list of this network's parameters
	 */
	public OrderedMap<GlobalVariable> getParameters() {
		return parameters;
	}

	/**
	 * Returns a map that associates each connection to its source vertex.
	 * 
	 * @return a map that associates each connection to its source vertex
	 */
	public Map<Connection, Vertex> getSourceMap() {
		return sourceMap;
	}

	/**
	 * Returns a map that associates each connection to its target vertex.
	 * 
	 * @return a map that associates each connection to its target vertex
	 */
	public Map<Connection, Vertex> getTargetMap() {
		return targetMap;
	}

	/**
	 * Returns the list of this network's variables
	 * 
	 * @return the list of this network's variables
	 */
	public OrderedMap<GlobalVariable> getVariables() {
		return variables;
	}

	/**
	 * Walks through the hierarchy, instantiate actors, and checks that
	 * connections actually point to ports defined in actors. Instantiating an
	 * actor implies first loading it and then giving it the right parameters.
	 * 
	 * @throws OrccException
	 *             if an actor could not be instantiated, or a connection is
	 *             wrong
	 */
	public void instantiate() throws OrccException {
		new Instantiator().transform(this);
	}

	/**
	 * Merges actors of this network. Note that for this transformation to work
	 * properly, actors must have been classified and normalized first.
	 * 
	 * @throws OrccException
	 *             if something goes wrong
	 */
	public void mergeActors() throws OrccException {
		new ActorMerger().transform(this);
	}

	/**
	 * Normalizes actors of this network so they can later be merged. Note that
	 * for this transformation to work properly, actors must have been
	 * classified first.
	 * 
	 * @throws OrccException
	 *             if something goes wrong
	 */
	public void normalizeActors() throws OrccException {
		new ActorNormalizer().transform(this);
	}

	@Override
	public String toString() {
		return name;
	}

}
