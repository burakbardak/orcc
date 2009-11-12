/*
 * Copyright(c)2008, Jani Boutellier, Christophe Lucarz, Veeranjaneyulu Sadhanala 
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the EPFL and University of Oulu nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY  Jani Boutellier, Christophe Lucarz, 
 * Veeranjaneyulu Sadhanala ``AS IS'' AND ANY 
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL  Jani Boutellier, Christophe Lucarz, 
 * Veeranjaneyulu Sadhanala BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package net.sf.orcc.backends.c.quasistatic.core.org.efsmScheduler.sim;

/**
 * This class represents variables used in the actor description.
 * @author sadhanal
 *
 */
public class Variable {
	String name;
	VarType type;
	int value;

    /**
     * Default constructor
     */
	public Variable(){
		name = null;
		type = VarType.NULL;
		value = 0;
	}

    /**
     * Constructor
     *
     * @param name name of variable
     * @param type type of variable
     * @param value value of variable
     */
	public Variable(String name, VarType type, int value) {
		super();
		this.name = name;
		this.type = type;
		this.value = value;
	}

    /**
     * Constructor
     * @param v
     */
	public Variable(Variable v){
		this.name = v.name;
		this.type = v.type;
		this.value = v.value;
	}

    /**
     *
     * @return value
     */
	public int getValue() {
		return value;
	}

    /**
     * Sets value
     * @param value
     */
	public void setValue(int value) {
		this.value = value;
	}
    /**
     *
     * @return name = value
     */
	public String  toString(){
		return name+"="+value;
	}
	
}

