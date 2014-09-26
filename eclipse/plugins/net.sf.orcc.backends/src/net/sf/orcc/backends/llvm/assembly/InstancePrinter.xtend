 package net.sf.orcc.backends.llvm.assembly

import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import net.sf.orcc.OrccRuntimeException
import net.sf.orcc.backends.BackendsConstants
import net.sf.orcc.backends.ir.ExprNull
import net.sf.orcc.backends.ir.InstCast
import net.sf.orcc.df.Action
import net.sf.orcc.df.Actor
import net.sf.orcc.df.Connection
import net.sf.orcc.df.FSM
import net.sf.orcc.df.Instance
import net.sf.orcc.df.Pattern
import net.sf.orcc.df.Port
import net.sf.orcc.df.State
import net.sf.orcc.df.Transition
import net.sf.orcc.ir.Arg
import net.sf.orcc.ir.ArgByVal
import net.sf.orcc.ir.Block
import net.sf.orcc.ir.BlockBasic
import net.sf.orcc.ir.BlockIf
import net.sf.orcc.ir.BlockWhile
import net.sf.orcc.ir.CfgNode
import net.sf.orcc.ir.ExprVar
import net.sf.orcc.ir.Expression
import net.sf.orcc.ir.InstAssign
import net.sf.orcc.ir.InstCall
import net.sf.orcc.ir.InstLoad
import net.sf.orcc.ir.InstPhi
import net.sf.orcc.ir.InstReturn
import net.sf.orcc.ir.InstStore
import net.sf.orcc.ir.Instruction
import net.sf.orcc.ir.Param
import net.sf.orcc.ir.Procedure
import net.sf.orcc.ir.Type
import net.sf.orcc.ir.TypeList
import net.sf.orcc.ir.Var
import net.sf.orcc.util.OrccLogger
import net.sf.orcc.util.util.EcoreHelper
import org.eclipse.emf.common.util.EList

import static net.sf.orcc.backends.BackendsConstants.*
import static net.sf.orcc.util.OrccAttributes.*

/*
 * Compile Instance llvm source code
 *
 * @author Antoine Lorence
 * @author Burak Bardak
 */
class InstancePrinter extends LLVMTemplate {

	protected var Instance instance
	protected var Actor actor
	protected var Map<Port, Connection> incomingPortMap
	protected var Map<Port, List<Connection>> outgoingPortMap
	protected var String name

	val Map<State, Integer> stateToLabel = new HashMap<State, Integer>
	val Map<Pattern, Map<Port, Integer>> portToIndexByPatternMap = new HashMap<Pattern, Map<Port, Integer>>

	protected var optionInline = false
	protected var optionDatalayout = BackendsConstants::LLVM_DEFAULT_TARGET_DATALAYOUT
	protected var optionArch = BackendsConstants::LLVM_DEFAULT_TARGET_TRIPLE

	protected var boolean isActionAligned = false

	new() {
		super()
	}

	/**
	 * Default constructor, do not activate profile option
	 */
	new(Map<String, Object> options) {
		super(options)
	}

	override setOptions(Map<String, Object> options) {
		super.setOptions(options)

		if(options.containsKey(INLINE)){
			optionInline = options.get(INLINE) as Boolean
		}
		if(options.containsKey(BackendsConstants::LLVM_TARGET_TRIPLE)){
			optionArch = options.get(BackendsConstants::LLVM_TARGET_TRIPLE) as String
		}
		if(options.containsKey(BackendsConstants::LLVM_TARGET_DATALAYOUT)){
			optionDatalayout = options.get(BackendsConstants::LLVM_TARGET_DATALAYOUT) as String
		}
	}

	/**
	 * Print file content from a given instance
	 *
	 * @param targetFolder folder to print the instance file
	 * @param instance the given instance
	 * @return 1 if file was cached, 0 if file was printed
	 */
	@Deprecated
	def print(String targetFolder, Instance instance) {
		setInstance(instance)
		print(targetFolder)
	}

	def setInstance(Instance instance) {
		if (!instance.isActor) {
			throw new OrccRuntimeException("Instance " + instance.name + " is not an Actor's instance")
		}

		this.instance = instance
		this.name = instance.name
		this.actor = instance.getActor
		this.incomingPortMap = instance.incomingPortMap
		this.outgoingPortMap = instance.outgoingPortMap

	}

	def setActor(Actor actor) {
		this.name = actor.name
		this.actor = actor
		this.incomingPortMap = actor.incomingPortMap
		this.outgoingPortMap = actor.outgoingPortMap
	}

	def getContent() '''
		«val inputs = actor.inputs.notNative»
		«val outputs = actor.outputs.notNative»
		«printDatalayout»
		«printArchitecture»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; Generated from "«actor.name»"
		declare i32 @printf(i8* noalias , ...) nounwind

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; FIFOs
		
		«FOR port : inputs»
			«val connection = incomingPortMap.get(port)»
			«connection.printExternalFifo(port)»
		«ENDFOR»

		«FOR port : outputs»
			«FOR connection : outgoingPortMap.get(port)»
				«IF !incomingPortMap.values.contains(connection)»
					«connection.printExternalFifo(port)»
				«ENDIF»
			«ENDFOR»
		«ENDFOR»
		
		«FOR port : inputs»
			«val connection = incomingPortMap.get(port)»
			«connection.printInput(port)»
		«ENDFOR»

		«FOR port : outputs»
			«FOR connection : outgoingPortMap.get(port)»
				«connection.printOutput(port)»
			«ENDFOR»
		«ENDFOR»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; Parameters
		«IF instance != null»
			«FOR arg : instance.arguments»
				@«arg.variable.name» = internal global «arg.variable.type.doSwitch» «arg.value.doSwitch»
			«ENDFOR»
		«ELSE»
			«FOR param : actor.parameters»
				«param.declare»
			«ENDFOR»
		«ENDIF»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; State variables
		«FOR variable : actor.stateVars»
			«variable.declare»
		«ENDFOR»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; Functions/procedures
		«FOR proc : actor.procs»
			«proc.print»

		«ENDFOR»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; Initializes
		«FOR init : actor.initializes»
			«init.print»

		«ENDFOR»

		;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		; Actions
		«FOR action : actor.actions»
			«action.print»

		«ENDFOR»

	'''

	def protected printDatalayout() '''target datalayout = "«optionDatalayout»"'''

	def protected printArchitecture() '''target triple = "«optionArch»"'''

	
	def protected print(Action action) {
		isActionAligned = false
		'''
		define internal «action.scheduler.returnType.doSwitch» @«action.scheduler.name»() nounwind {
		entry:
			«FOR local : action.scheduler.locals»
				«local.declare»
			«ENDFOR»
			«FOR port : action.peekPattern.ports.notNative»
				«port.loadVar(incomingPortMap.get(port), action.body.name)»
			«ENDFOR»
			br label %b«action.scheduler.blocks.head.label»

		«FOR block : action.scheduler.blocks»
			«block.doSwitch»
		«ENDFOR»
		}
		
		«IF !action.hasAttribute(ALIGNED_ALWAYS)»
			«printCore(action, false)»
		«ENDIF»
		«IF isActionAligned = action.hasAttribute(ALIGNABLE)»
			«printCore(action, true)»
		«ENDIF»
		'''
	}
	
	def protected printCore(Action action, boolean isAligned) '''
		«val inputPattern = action.inputPattern»
		«val outputPattern = action.outputPattern»
		define internal «action.body.returnType.doSwitch» @«action.body.name»«IF isAligned»_aligned«ENDIF»() «IF optionInline»noinline «ENDIF»nounwind {
		entry:
			«FOR local : action.body.locals»
				«local.declare»
			«ENDFOR»
			«FOR port : inputPattern.ports.notNative»
				«port.loadVar(incomingPortMap.get(port), action.body.name)»
			«ENDFOR»
			«FOR port : outputPattern.ports.notNative»
				«FOR connection : outgoingPortMap.get(port)»
					«port.loadVar(connection, action.body.name)»
				«ENDFOR»
			«ENDFOR»
			br label %b«action.body.blocks.head.label»

		«FOR block : action.body.blocks»
			«block.doSwitch»
		«ENDFOR»
			«FOR port : inputPattern.ports.notNative»
				«port.updateVar(incomingPortMap.get(port), inputPattern.getNumTokens(port), action.body.name)»
			«ENDFOR»
			«FOR port : outputPattern.ports.notNative»
				«FOR connection : outgoingPortMap.get(port)»
					«port.updateVar(connection, outputPattern.getNumTokens(port), action.body.name)»
				«ENDFOR»
			«ENDFOR»
			ret void
		}
	'''

	def protected loadVar(Port port, Connection connection, String actionName) '''
		%local_size_«port.name»_«connection.getSafeId(port)» = load i32* @SIZE_«port.name»_«connection.getSafeId(port)»
		«IF (isActionAligned && port.hasAttribute(actionName + "_" + ALIGNABLE)) || port.hasAttribute(ALIGNED_ALWAYS)»
			%orig_local_index_«port.name»_«connection.getSafeId(port)» = load i32* @index_«port.name»_«connection.getSafeId(port)»
			%local_index_«port.name»_«connection.getSafeId(port)» = urem i32 %orig_local_index_«port.name»_«connection.getSafeId(port)», %local_size_«port.name»_«connection.getSafeId(port)»
		«ELSE»
			%local_index_«port.name»_«connection.getSafeId(port)» = load i32* @index_«port.name»_«connection.getSafeId(port)»
		«ENDIF»
	'''

	def protected updateVar(Port port, Connection connection, Integer numTokens, String actionName) '''
		«IF (isActionAligned && port.hasAttribute(actionName + "_" + ALIGNABLE)) || port.hasAttribute(ALIGNED_ALWAYS)»
			%new_index_«port.name»_«connection.getSafeId(port)» = add i32 %orig_local_index_«port.name»_«connection.getSafeId(port)», «numTokens»
		«ELSE»
			%new_index_«port.name»_«connection.getSafeId(port)» = add i32 %local_index_«port.name»_«connection.getSafeId(port)», «numTokens»
		«ENDIF»
		store i32 %new_index_«port.name»_«connection.getSafeId(port)», i32* @index_«port.name»_«connection.getSafeId(port)»
	'''

	def protected print(Procedure procedure) '''
		«val parameters = procedure.parameters.join(", ")[declare]»
		«IF procedure.native || procedure.blocks.nullOrEmpty»
			declare «procedure.returnType.doSwitch» @«procedure.name»(«parameters») nounwind
		«ELSE»
			define internal «procedure.returnType.doSwitch» @«procedure.name»(«parameters») nounwind {
			entry:
			«FOR local : procedure.locals»
				«local.declare»
			«ENDFOR»
				br label %b«procedure.blocks.head.label»

			«FOR block : procedure.blocks»
				«block.doSwitch»
			«ENDFOR»
			}
		«ENDIF»
	'''

	def protected label(Block block) '''b«block.cfgNode.number»'''

	def protected declare(Var variable) {
		if(variable.global)
			'''@«variable.name» = internal «IF variable.assignable»global«ELSE»constant«ENDIF» «variable.type.doSwitch» «variable.initialize»'''
	}

	def protected initialize(Var variable) {
		if(variable.initialValue != null) variable.initialValue.doSwitch
		else "zeroinitializer"
	}

	def protected declare(Param param) {
		val pName = param.variable.name
		val pType = param.variable.type
		if (pType.string) '''i8* %«pName»'''
		else if (pType.list) '''«pType.doSwitch»* noalias %«pName»'''
		else '''«pType.doSwitch» %«pName»'''
	}

	def private printInput(Connection connection, Port port) '''
		«val id = connection.getSafeId(port)»
		«val name = port.name + "_" + id»
		«val addrSpace = connection.addrSpace»
		«val prop = port.properties»

		@SIZE_«name» = internal constant i32 «connection.safeSize»
		@index_«name» = internal global i32 0
		@numTokens_«name» = internal global i32 0

		define internal void @read_«name»() {
		entry:
			br label %read

		read:
			%rdIndex = load«prop» i32«addrSpace»* @fifo_«id»_rdIndex
			store i32 %rdIndex, i32* @index_«name»
			%wrIndex = load«prop» i32«addrSpace»* @fifo_«id»_wrIndex
			%getNumTokens = sub i32 %wrIndex, %rdIndex
			%numTokens = add i32 %rdIndex, %getNumTokens
			store i32 %numTokens, i32* @numTokens_«name»
			ret void
		}

		define internal void @read_end_«name»() {
		entry:
			br label %read_end

		read_end:
			%rdIndex = load i32* @index_«name»
			store«prop» i32 %rdIndex, i32«addrSpace»* @fifo_«id»_rdIndex
			ret void
		}
	'''

	def private printOutput(Connection connection, Port port) '''
		«val id = connection.getSafeId(port)»
		«val name = port.name + "_" + id»
		«val addrSpace = connection.addrSpace»
		«val prop = port.properties»

		@SIZE_«name» = internal constant i32 «connection.safeSize»
		@index_«name» = internal global i32 0
		@rdIndex_«name» = internal global i32 0
		@numFree_«name» = internal global i32 0

		define internal void @write_«name»() {
		entry:
			br label %write

		write:
			%wrIndex = load«prop» i32«addrSpace»* @fifo_«id»_wrIndex
			store i32 %wrIndex, i32* @index_«name»
			%rdIndex = load«prop» i32«addrSpace»* @fifo_«id»_rdIndex
			store i32 %rdIndex, i32* @rdIndex_«name»
			%size = load i32* @SIZE_«name»
			%numTokens = sub i32 %wrIndex, %rdIndex
			%getNumFree = sub i32 %size, %numTokens
			%numFree = add i32 %wrIndex, %getNumFree
			store i32 %numFree, i32* @numFree_«name»
			ret void
		}

		define internal void @write_end_«name»() {
		entry:
			br label %write_end

		write_end:
			%wrIndex = load i32* @index_«name»
			store«prop» i32 %wrIndex, i32«addrSpace»* @fifo_«id»_wrIndex
			ret void
		}
	'''

	/**
	 * Returns an annotation describing the address space.
	 * This annotation is required by the TTA backend.
	 */
	def protected getAddrSpace(Connection connection) ''''''

	/**
	 * Returns an annotation describing the properties of the access.
	 * This annotation is required by the TTA backend.
	 */
	def protected getProperties(Port port) ''''''

	def private printExternalFifo(Connection conn, Port port) {
		val fifoName = "fifo_" + conn.getSafeId(port)
		val type = port.type.doSwitch
		if(conn != null) {
			val addrSpace = conn.addrSpace
			'''
			@«fifoName»_content = external«addrSpace» global [«conn.safeSize» x «type»]
			@«fifoName»_rdIndex = external«addrSpace» global i32
			@«fifoName»_wrIndex = external«addrSpace» global i32
			'''
		} else {
			OrccLogger::noticeln("["+name+"] Port "+port.name+" not connected.")
			'''
			@«fifoName»_content = internal global [«conn.safeSize» x «type»] zeroinitializer
			@«fifoName»_rdIndex = internal global i32 zeroinitializer
			@«fifoName»_wrIndex = internal global i32 zeroinitializer
			'''
		}
	}

	def private getNextLabel(Block block) {
		if (block.blockWhile) (block as BlockWhile).joinBlock.label
		else block.label
	}

	override caseBlockBasic(BlockBasic blockBasic) '''
		b«blockBasic.label»:
			«FOR instr : blockBasic.instructions»
				«instr.doSwitch»
			«ENDFOR»
			«IF ! blockBasic.cfgNode.successors.empty»
				br label %b«(blockBasic.cfgNode.successors.head as CfgNode).node.nextLabel»
			«ENDIF»
	'''

	override caseBlockIf(BlockIf blockIf) '''
		b«blockIf.label»:
			br i1 «blockIf.condition.doSwitch», label %b«blockIf.thenBlocks.head.nextLabel», label %b«blockIf.elseBlocks.head.nextLabel»

		«FOR block : blockIf.thenBlocks»
			«block.doSwitch»
		«ENDFOR»

		«FOR block : blockIf.elseBlocks»
			«block.doSwitch»
		«ENDFOR»

		«blockIf.joinBlock.doSwitch»
	'''

	override caseInstruction(Instruction instr) {
			super.caseInstruction(instr)
	}

	override caseExpression(Expression expr) {
		if(expr instanceof ExprNull)
			return caseExprNull(expr as ExprNull)
		else
			super.caseExpression(expr)
	}

	def caseExprNull(ExprNull expr) '''null'''


	override caseInstAssign(InstAssign assign)
		'''%«assign.target.variable.name» = «assign.value.doSwitch»'''

	override caseInstPhi(InstPhi phi)
		'''«phi.target.variable.print» = phi «phi.target.variable.type.doSwitch» «phi.phiPairs»'''

	def private getPhiPairs(InstPhi phi)
		'''«printPhiExpr(phi.values.head, (phi.block.cfgNode.predecessors.head as CfgNode).node)», «printPhiExpr(phi.values.tail.head, (phi.block.cfgNode.predecessors.tail.head as CfgNode).node)»'''

	def private printPhiExpr(Expression expr, Block block)
		'''[«expr.doSwitch», %b«block.label»]'''

	override caseInstReturn(InstReturn retInst) {
		val action = EcoreHelper::getContainerOfType(retInst, typeof(Action))
		if ( action == null || EcoreHelper::getContainerOfType(retInst, typeof(Procedure)) == action.scheduler) {
			if(retInst.value == null)
				'''ret void'''
			else
				'''ret «retInst.value.type.doSwitch» «retInst.value.doSwitch»'''
		}
	}

	override caseInstStore(InstStore store) {
		val action = EcoreHelper::getContainerOfType(store, typeof(Action))
		val variable = store.target.variable
		'''
			«IF variable.type.list»
				«val innerType = (variable.type as TypeList).innermostType»
				«IF action != null && action.outputPattern.contains(variable) && ! action.outputPattern.varToPortMap.get(variable).native»
					«val port = action.outputPattern.varToPortMap.get(variable)»
					«FOR connection : outgoingPortMap.get(port)»
						store«port.properties» «innerType.doSwitch» «store.value.doSwitch», «innerType.doSwitch»«connection.addrSpace»* «varName(variable, store)»_«connection.getSafeId(port)»
					«ENDFOR»
				«ELSE»
					store «innerType.doSwitch» «store.value.doSwitch», «innerType.doSwitch»* «varName(variable, store)»
				«ENDIF»
			«ELSE»
				store «variable.type.doSwitch» «store.value.doSwitch», «variable.type.doSwitch»* «variable.print»
			«ENDIF»
		'''
	}

	override caseInstLoad(InstLoad load) {
		val action = EcoreHelper::getContainerOfType(load, typeof(Action))
		val variable = load.source.variable
		val target = load.target.variable.print
		'''
			«IF variable.type.list»
				«val innerType = (variable.type as TypeList).innermostType»
				«IF action != null && action.inputPattern.contains(variable) && ! action.inputPattern.varToPortMap.get(variable).native»
					«val port = action.inputPattern.varToPortMap.get(variable)»
					«val connection = incomingPortMap.get(port)»
					«target» = load«port.properties» «innerType.doSwitch»«connection.addrSpace»* «varName(variable, load)»_«connection.getSafeId(port)»
				«ELSEIF action != null && action.outputPattern.contains(variable) && ! action.outputPattern.varToPortMap.get(variable).native»
					«val port = action.outputPattern.varToPortMap.get(variable)»
					«val connection = outgoingPortMap.get(port).head»
					«target» = load«port.properties» «innerType.doSwitch»«connection.addrSpace»* «varName(variable, load)»_«connection.getSafeId(port)»
				«ELSEIF action != null && action.peekPattern.contains(variable)»
					«val port = action.peekPattern.varToPortMap.get(variable)»
					«val connection = incomingPortMap.get(port)»
					«target» = load«port.properties» «innerType.doSwitch»«connection.addrSpace»* «varName(variable, load)»_«connection.getSafeId(port)»
				«ELSE»
					«target» = load «innerType.doSwitch»* «varName(variable, load)»
				«ENDIF»
			«ELSE»
				«target» = load «variable.type.doSwitch»* «variable.print»
			«ENDIF»
		'''
	}


	override caseInstCall(InstCall call) '''
		«IF call.print»
			call i32 (i8*, ...)* @printf(«call.arguments.join(", ")[printArgument((it as ArgByVal).value.type)]»)
		«ELSE»
			«IF call.target != null»%«call.target.variable.name» = «ENDIF»call «call.procedure.returnType.doSwitch» @«call.procedure.name» («call.arguments.format(call.procedure.parameters).join(", ")»)
		«ENDIF»
	'''

	def protected format(EList<Arg> args, EList<Param> params) {
		val paramList = new ArrayList<CharSequence>
		if(params.size != 0) {
			for (i : 0..params.size-1) {
				paramList.add(printArgument(args.get(i), params.get(i).variable.type))
			}
		}
		return paramList
	}

	def protected printArgument(Arg arg, Type type) {
		if (arg.byRef)
			'''TODO'''
		else if (type.string) {
			val expr = (arg as ArgByVal).value as ExprVar
			'''i8* «IF expr.use.variable.local» «expr.doSwitch» «ELSE» getelementptr («expr.type.doSwitch»* «expr.doSwitch», i32 0, i32 0)«ENDIF»'''
		} else
			'''«type.doSwitch»«IF type.list»*«ENDIF» «(arg as ArgByVal).value.doSwitch»'''
	}


	def protected varName(Var variable, Instruction instr) {
		val procedure = EcoreHelper::getContainerOfType(instr, typeof(Procedure))
		'''%«variable.name»_elt_«(procedure.getAttribute("accessMap").objectValue as Map<Instruction, Integer>).get(instr)»'''
	}




}