package net.sf.orcc.backends.c.dal

import net.sf.orcc.backends.c.CTemplate
import net.sf.orcc.df.Connection
import net.sf.orcc.df.Entity
import net.sf.orcc.df.Network
import net.sf.orcc.graph.Vertex
import net.sf.orcc.ir.Type

/**
 * Generate and print process network description for DAL backend.
 *  
 * @author Jani Boutellier (University of Oulu)
 * 
 * Modified from Orcc C NetworkPrinter
 */
class NetworkCPrinter extends CTemplate {

	protected var Network network

	def setNetwork(Network network) {
		this.network = network
	}

	def getFifoSizeHeaderContent() '''
		#define FIFO_SIZE «fifoSize»
	'''

	def getNetworkFileContent() '''
		<?xml version="1.0" encoding="UTF-8"?>
		<processnetwork xmlns="http://www.tik.ee.ethz.ch/~euretile/schema/PROCESSNETWORK" 
		xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" 
		xsi:schemaLocation="http://www.tik.ee.ethz.ch/~euretile/schema/PROCESSNETWORK
		http://www.tik.ee.ethz.ch/~euretile/schema/processnetwork.xsd" name="«network.name»">
		
			«FOR actor : network.getAllActors»
				«val actorType = if(actor.inputs.size > 0 && actor.outputs.size > 0) '''local''' else '''io'''»
				<process name="«actor.name»" type="«actorType»"> 
				«FOR port : actor.inputs»
					<port type="input" name="«port.getNumber»"/>
				«ENDFOR»
				«FOR port : actor.outputs»
					<port type="output" name="«port.getNumber»"/>
				«ENDFOR»
				<source type="c" location="«actor.name».c"/>
				</process>
				
			«ENDFOR»
			«FOR child : network.children»
				«child.allocateFifos»
			«ENDFOR»
			«FOR child : network.children»
				«child.assignFifo»
			«ENDFOR»
		</processnetwork>
	'''
	
	def protected assignFifo(Vertex vertex) '''
		«FOR inList : vertex.getAdapter(typeof(Entity)).incomingPortMap.values»
			<connection name="C«inList.<Integer>getValueAsObject("idNoBcast")»-«inList.targetPort.getNumber»">
				<origin name="C«inList.<Integer>getValueAsObject("idNoBcast")»">
					<port name="1"/>
				</origin>
				<target name="«inList.target.label»">
					<port name="«inList.targetPort.getNumber»"/>
				</target>
			</connection>
		«ENDFOR»

		«FOR outList : vertex.getAdapter(typeof(Entity)).outgoingPortMap.values»
			<connection name="«outList.get(0).sourcePort.getNumber»-C«outList.head.<Integer>getValueAsObject("idNoBcast")»">
				<origin name="«vertex.label»">
					<port name="«outList.get(0).sourcePort.getNumber»"/>
				</origin>
				<target name="C«outList.head.<Integer>getValueAsObject("idNoBcast")»">
					<port name="0"/>
				</target>
			</connection>
		«ENDFOR»
			
	'''

	def protected allocateFifos(Vertex vertex) '''
		«FOR connectionList : vertex.getAdapter(typeof(Entity)).outgoingPortMap.values»
			«allocateFifo(connectionList.get(0), connectionList.size)»
		«ENDFOR»
	'''
	
	def private int sizeOf(Type type) {
		if (type.float) {
			return 4
		} else if (type.int || type.uint){
			if (type.getSizeInBits() > 16) {
				return 4
			} else if (type.getSizeInBits() > 8) {
				return 2
			}
		}
		return 1
	}
	
	def protected allocateFifo(Connection conn, int nbReaders) '''
		<sw_channel type="fifo" size="«if (conn.size != null) conn.size*sizeOf(conn.getSourcePort().getType()) else fifoSize»" name="C«conn.<Object>getValueAsObject("idNoBcast")»">
			<port type="input" name="0"/>
			<port type="output" name="1"/>
		</sw_channel>
		
	'''
}