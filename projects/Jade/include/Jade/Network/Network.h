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

/**
@brief Description of the Network class interface
@author Jerome Gorin
@file Network.h
@version 0.1
@date 22/03/2010
*/

//------------------------------
#ifndef NETWORK_H
#define NETWORK_H

#include <map>
#include <list>
#include <string>

class Port;
class Instance;
class HDAGGraph;
class Actor;
//------------------------------

/**
*
* @class Network
* @brief  This class defines a XDF network.
*
* @author Jerome Gorin
*
*/
class Network {

public:

	/*!
     *  @brief Return a list of the Actor contained in the network.
     *
     *  Return all Actors of the current network.
	 *   
	 *
     *  @return a map of Actor contained in the network
     */
	std::list<Actor*>* getActors();

	/*!
     *  @brief Return a list of the Instance contained in the network.
     *
     *  Return all Instance of the current network.
	 *   
	 *
     *  @return a map of Actor contained in the network
     */
	std::map<std::string, Instance*>* getInstances();


	/*!
     *  @brief Create a network.
	 *
	 * Creates a new network with the given name, inputs, outputs, and graph.
	 * 
	 * @param name : network name
	 *
	 * @param inputs : map of input ports
	 *
	 * @param outputs : map of output ports
	 *
	 * @param graph : graph representing network
	 */
	Network(std::string name, std::map<std::string, Port*>* inputs, std::map<std::string, Port*>* outputs, HDAGGraph* graph);


	/**
	 * @brief Getter of graph
	 *
	 * Returns the graph representing the network's contents
	 * 
	 * @return HDAGGraph representing the network's contents
	 */
	HDAGGraph* getGraph() {	return graph;};

	/*!
     *  @brief Print network in a dot file.
	 *
	 *  Output the parsed network into a dot file.
	 *
	 *  @param file : file to print the dot into
	 */
	void print(std::string file);

private:

	/** name of the network  */
	std::string name;

	/** map of input ports  */
	std::map<std::string, Port*>* inputs;

	/** map of outputs ports  */
	std::map<std::string, Port*>* outputs;

	/** graph of the network  */
	HDAGGraph* graph;

	/** actors of the network  */
	std::list<Actor*> actors;
	
	/** instances of the network  */
	std::map<std::string, Instance*> instances;

};

#endif