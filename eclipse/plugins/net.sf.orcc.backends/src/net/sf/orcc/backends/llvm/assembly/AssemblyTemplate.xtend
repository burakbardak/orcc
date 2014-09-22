/*
 * Copyright (c) 2012, IETR/INSA of Rennes
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
 * about
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
package net.sf.orcc.backends.llvm.assembly

import java.util.Map
import net.sf.orcc.OrccRuntimeException
import net.sf.orcc.backends.CommonPrinter
import net.sf.orcc.df.Connection
import net.sf.orcc.df.Port
import net.sf.orcc.ir.ExprBinary
import net.sf.orcc.ir.ExprBool
import net.sf.orcc.ir.ExprInt
import net.sf.orcc.ir.ExprList
import net.sf.orcc.ir.ExprString
import net.sf.orcc.ir.ExprUnary
import net.sf.orcc.ir.ExprVar
import net.sf.orcc.ir.OpBinary
import net.sf.orcc.ir.Type
import net.sf.orcc.ir.TypeBool
import net.sf.orcc.ir.TypeFloat
import net.sf.orcc.ir.TypeInt
import net.sf.orcc.ir.TypeList
import net.sf.orcc.ir.TypeString
import net.sf.orcc.ir.TypeUint
import net.sf.orcc.ir.TypeVoid
import net.sf.orcc.ir.Var
import net.sf.orcc.ir.util.TypeUtil

/*
 * Default LLVM Printer. Call ExpressionPrinter when necessary and print data types.
 *  
 * @author Antoine Lorence
 * @author Burak Bardak
 */
abstract class LLVMTemplate extends CommonPrinter {
	
	var Type currentType = null
	protected var signed = false
	protected var floating = false

	new() {
		super()
	}

	new(Map<String, Object> options) {
		super(options)
	}

	/////////////////////////////////
	// Expressions Register to Register -- OpBinary
	/////////////////////////////////
	
	override stringRepresentation(OpBinary op) {
		switch (op) {
//			case OpBinary::NOP:"NOP"		
			case OpBinary::PLUS:
				if (floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else 					"ADD"
			case OpBinary::MINUS:
				if (floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else 					"SUB"	
			case OpBinary::TIMES:
				if(floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else 					"MUL"	
// ---------------------------------------------------------------------------------------------These are going to be replaced by optimization transformations... 
//			case OpBinary::MUL_ADD
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"MULADD"
//			case OpBinary::MUL_SUB
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"MULSUB"
//			case OpBinary::MUL_ACC
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"MULACC"
			case OpBinary::BITAND: 		
				if(floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else					"LAND"
			case OpBinary::BITXOR: 		
				if(floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else					"LXOR"
//			case OpBinary::BITXNR: 			
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"LXNR"					
			case OpBinary::BITOR:
				if(floating)
				throw new OrccRuntimeException("Floating operation is not supported" + op)
				else					"LOR"
//			case OpBinary::LNOR:
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"LNOR"
//			case OpBinary::LNOT:
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"LNOT"
//			case OpBinary::LNAND:
//				if(floating)
//				throw new OrccRuntimeException("Floating operation is not supported" + op)
//				else					"LNAND"
			case OpBinary::SHIFT_LEFT:	"LSL"
			case OpBinary::SHIFT_RIGHT:	"LSR"

			case OpBinary::DIV:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::DIV_INT:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::EQ:
				throw new OrccRuntimeException("Operation is not supported :" + op)			
			case OpBinary::EXP:
				throw new OrccRuntimeException("Operation is not supported :" + op)			
			case OpBinary::GE:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::GT:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::LOGIC_AND:
				throw new OrccRuntimeException("Operation is not supported :" + op)			
			case OpBinary::LE:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::LT:
				throw new OrccRuntimeException("Operation is not supported :" + op)			
			case OpBinary::MOD:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			case OpBinary::NE:
				throw new OrccRuntimeException("Operation is not supported :" + op)
			default:
				throw new OrccRuntimeException("Unknown binary operator : " + op)
		}
	}
	
	
	override caseExprBinary(ExprBinary expr) {
		val op = expr.op
		val e1 = expr.e1
		val e2 = expr.e2
		var Type type
		
		if (op == OpBinary::SHIFT_RIGHT) {
			type = e1.type;
		} else {
			type = TypeUtil.getLub(e1.type, e2.type);
		}
		if (type == null) {
			throw new OrccRuntimeException(
				"Type mismatch: cannot evaluate the least upper bound between " 
				+ e1.type + " and " + e2.type);
		}

		signed = !type.uint
		floating = type.float

		'''«op.stringRepresentation» «e1.type.doSwitch» «e1.doSwitch», «e2.doSwitch»'''
	}
	
	override caseExprUnary(ExprUnary expr) {
		throw new OrccRuntimeException("No unary expression in LLVM")
	}
	
	override caseExprString(ExprString expr) {
		'''c«super.caseExprString(expr)»'''
	}
	
	override caseExprVar(ExprVar expr) {
		expr.use.variable.print
	}
		
	override caseExprList(ExprList exprList) {
		val prevType = currentType
		
		currentType = 
			if (exprList.eContainer instanceof Var) 
				((exprList.eContainer as Var).type as TypeList).type
			else
				(currentType as TypeList).type

		
		val list = '''[«exprList.value.join(", ")['''«currentType.doSwitch» «doSwitch»''']»]'''
		currentType = prevType
		return list.wrap
	}
	
	override caseExprBool(ExprBool expr) {
		if(expr.value) "1" else "0"
	}
	
	override caseExprInt(ExprInt expr) {
		expr.value.toString
	}
	
	/////////////////////////////////
	// Types
	/////////////////////////////////
	
	override caseTypeBool(TypeBool type) 
		'''i1'''

	override caseTypeInt(TypeInt type)
		'''i«type.size»'''

	override caseTypeUint(TypeUint type) 
		'''i«type.size»'''

	override caseTypeFloat(TypeFloat type) {
		if (type.size == 16) '''half'''
		else if (type.size == 64) '''double'''
		else '''float'''
	}

	override caseTypeString(TypeString type) {
		if(type.size == 0) '''i8*''' 
		else '''[«type.size» x i8]'''
	}

	override caseTypeVoid(TypeVoid type)
		'''void'''
	
	override caseTypeList(TypeList typeList)
		'''[«typeList.size» x «typeList.type.doSwitch»]'''

	
	/******************************************
	 * 
	 * Helpers
	 *
	 *****************************************/
	
	def protected getSafeId(Connection connection, Port port) {
		connection?.getAttribute("id")?.objectValue ?: port.name
	}
	
	def protected print(Var variable)
		'''«IF variable.global»@«ELSE»%«ENDIF»«variable.name»'''
}