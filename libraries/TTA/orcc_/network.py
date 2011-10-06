#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2011, IRISA
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   * Redistributions of source code must retain the above copyright notice,
#     this list of conditions and the following disclaimer.
#   * Redistributions in binary form must reproduce the above copyright notice,
#     this list of conditions and the following disclaimer in the documentation
#     and/or other materials provided with the distribution.
#   * Neither the name of IRISA nor the names of its
#     contributors may be used to endorse or promote products derived from this
#     software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
# STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
# WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.
#
# @author Herve Yviquel

import os
import shutil
import stat

from .instance import *

class Network:

    def __init__(self, name, instances):
        self.name = name
        self.instances = instances


    def compile(self, srcPath, libPath, args, debug):
        for instance in self.instances:
            print ">> Instance " + instance.id + "."
            instance.compile(srcPath, libPath, args, debug)


    def simulate(self, srcPath, tracePath):
        for instance in self.instances:
            print ">> Instance " + instance.id + "."
            instance.simulate(srcPath, tracePath)


    def generate(self, srcPath, buildPath, libPath, args, debug):
        print "* Initialize the generation."
        shutil.copy(os.path.join(srcPath, "top.vhd"), buildPath)
        shutil.copy(os.path.join(srcPath, "top_tb.vhd"), buildPath)
        shutil.copy(os.path.join(srcPath, "top.qsf"), buildPath)
        shutil.copy(os.path.join(srcPath, "top.qpf"), buildPath)
        shutil.copy(os.path.join(srcPath, "top.tcl"), buildPath)
        os.chmod(os.path.join(buildPath, "top.tcl"), stat.S_IRWXU)
        iromAddrList = []
        dramAddrList = []

        for instance in self.instances:
            instance.initializeMemories(srcPath)
            iromAddrList.append(instance.irom.getAddr())
            dramAddrList.append(instance.dram.getAddr())

        iromAddrMax = max(iromAddrList)
        dramAddrMax = max(dramAddrList)

        shutil.rmtree(os.path.join(buildPath, "wrapper"), ignore_errors=True)
        shutil.copytree(os.path.join(libPath, "wrapper"), os.path.join(buildPath, "wrapper"))
        shutil.rmtree(os.path.join(buildPath, "simulation"), ignore_errors=True)
        shutil.copytree(os.path.join(libPath, "simulation"), os.path.join(buildPath, "simulation"))

        for instance in self.instances:
            print ">> Instance " + instance.id + "."
            instance.generate(srcPath, buildPath, libPath, iromAddrMax, dramAddrMax, args, debug)
