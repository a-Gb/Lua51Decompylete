'''
    lparser.py

    Depends on lundump.py for lua dump deserialization.

    An experimental bytecode decompiler.
'''

from lundump import Chunk, Constant, Instruction, Opcodes, whichRK, readRKasK


LUA_STDLIB = {
    "assert": "global",
    "collectgarbage": "global",
    "dofile": "global",
    "error": "global",
    "getmetatable": "global",
    "ipairs": "global",
    "load": "global",
    "loadfile": "global",
    "next": "global",
    "pairs": "global",
    "pcall": "global",
    "print": "global",
    "rawequal": "global",
    "rawget": "global",
    "rawset": "global",
    "select": "global",
    "setmetatable": "global",
    "tonumber": "global",
    "tostring": "global",
    "type": "global",
    "xpcall": "global",
    "require": "global",
    "coroutine.create": "coroutine",
    "coroutine.resume": "coroutine",
    "coroutine.running": "coroutine",
    "coroutine.status": "coroutine",
    "coroutine.wrap": "coroutine",
    "coroutine.yield": "coroutine",
    "string.byte": "string",
    "string.char": "string",
    "string.dump": "string",
    "string.find": "string",
    "string.format": "string",
    "string.gmatch": "string",
    "string.gsub": "string",
    "string.len": "string",
    "string.lower": "string",
    "string.match": "string",
    "string.rep": "string",
    "string.reverse": "string",
    "string.sub": "string",
    "string.upper": "string",
    "table.concat": "table",
    "table.insert": "table",
    "table.remove": "table",
    "table.sort": "table",
    "math.abs": "math",
    "math.acos": "math",
    "math.asin": "math",
    "math.atan": "math",
    "math.ceil": "math",
    "math.cos": "math",
    "math.deg": "math",
    "math.exp": "math",
    "math.floor": "math",
    "math.log": "math",
    "math.max": "math",
    "math.min": "math",
    "math.pi": "math",
    "math.rad": "math",
    "math.random": "math",
    "math.randomseed": "math",
    "math.sin": "math",
    "math.sqrt": "math",
    "math.tan": "math",
    "io.close": "io",
    "io.flush": "io",
    "io.input": "io",
    "io.lines": "io",
    "io.open": "io",
    "io.output": "io",
    "io.popen": "io",
    "io.read": "io",
    "io.tmpfile": "io",
    "io.type": "io",
    "io.write": "io",
    "os.clock": "os",
    "os.date": "os",
    "os.difftime": "os",
    "os.execute": "os",
    "os.exit": "os",
    "os.getenv": "os",
    "os.remove": "os",
    "os.rename": "os",
    "os.setlocale": "os",
    "os.time": "os",
    "os.tmpname": "os",
}


class _Scope:
    def __init__(self, startPC: int, endPC: int):
        self.startPC = startPC
        self.endPC = endPC

class _Traceback:
    def __init__(self):
        self.sets = []
        self.uses = []
        self.isConst = False

class _Line:
    def __init__(self, startPC: int, endPC: int, src: str, scope: int):
        self.startPC = startPC
        self.endPC = endPC
        self.src = src
        self.scope = scope

def isValidLocal(ident: str) -> bool:
    # has to start with an alpha or _
    if ident[0] not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_":
        return False

    # then it can be alphanum or _
    for c in ident[1:]:
        if c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890_":
            return False

    return True

class LuaDecomp:
    def __init__(self, chunk: Chunk, headChunk: bool = True, scopeOffset: int = 0):
        self.chunk = chunk
        self.pc = 0
        self.scope: list[_Scope] = []
        self.lines: list[_Line] = []
        self.top = {}
        self.locals = {}
        self.traceback = {}
        self.unknownLocalCount = 0
        self.headChunk = headChunk
        self.scopeOffset = scopeOffset # number of scopes this chunk/proto is in
        self.src: str = ""

        # Add these lines for type inference
        self.inferred_types = {}
        self.variable_usage = {}

        # configurations!
        self.aggressiveLocals = False # should *EVERY* set register be considered a local? 
        self.annotateLines = False
        self.indexWidth = 4 # how many spaces for indentions?

        self.__loadLocals()

        if not self.headChunk:
            functionProto = "function("

            # define params
            for i in range(self.chunk.numParams):
                functionProto += ("%s, " if i+1 < self.chunk.numParams else "%s") % self.__makeLocalIdentifier(i)
                self.__addSetTraceback(i)
            functionProto += ")"

            self.__startScope(functionProto, 0, len(self.chunk.instructions))


        # parse instructions
        while self.pc < len(self.chunk.instructions):
            self.parseInstr()
            self.pc += 1
            self.__checkScope()

        # Only end the scope if we're not in the head chunk and we have a scope to end
        if not self.headChunk and self.scope:
            self.__endScope()
            
    def __infer_type(self, reg):
        if reg in self.inferred_types:
            return self.inferred_types[reg]
        return "unknown"

    def __set_inferred_type(self, reg, type):
        self.inferred_types[reg] = type


    def getPseudoCode(self) -> str:
        self.__optimize_variable_scopes()
        
        fullSrc = ""
        for line in self.lines:
            if self.annotateLines:
                fullSrc += f"-- PC: {line.startPC} to PC: {line.endPC}\n"
            fullSrc += ((' ' * self.indexWidth) * (line.scope + self.scopeOffset)) + line.src + "\n"

        return fullSrc
    # =======================================[[ Helpers ]]=========================================
    def __analyze_control_flow(self):
        self.blocks = []
        current_block = []
        for pc, instr in enumerate(self.chunk.instructions):
            current_block.append((pc, instr))
            if instr.opcode in [Opcodes.JMP, Opcodes.EQ, Opcodes.LT, Opcodes.LE, Opcodes.TEST, Opcodes.TESTSET, Opcodes.FORLOOP, Opcodes.TFORLOOP]:
                self.blocks.append(current_block)
                current_block = []
        if current_block:
            self.blocks.append(current_block)
    def __add_comment(self, comment):
        self.__addExpr(f"  -- {comment}")
        self.__endStatement()

    def __getInstrAtPC(self, pc: int) -> Instruction:
        if pc < len(self.chunk.instructions):
            return self.chunk.instructions[pc]

        raise Exception("Decompilation failed!")

    def __getNextInstr(self) -> Instruction:
        return self.__getInstrAtPC(self.pc + 1)

    def __getCurrInstr(self) -> Instruction:
        return self.__getInstrAtPC(self.pc)

    def __makeTracIfNotExist(self) -> None:
        if not self.pc in self.traceback:
            self.traceback[self.pc] = _Traceback()

    # when we read from a register, call this
    def __addUseTraceback(self, reg: int) -> None:
        self.__makeTracIfNotExist()
        self.traceback[self.pc].uses.append(reg)

    # when we write from a register, call this
    def __addSetTraceback(self, reg: int) -> None:
        self.__makeTracIfNotExist()
        self.traceback[self.pc].sets.append(reg)

    def __addExpr(self, code: str) -> None:
        self.src += code

    def __endStatement(self):
        startPC = self.lines[len(self.lines) - 1].endPC + 1 if len(self.lines) > 0 else 0
        endPC = self.pc

        # make sure we don't write an empty line
        if not self.src == "":
            self.lines.append(_Line(startPC, endPC, self.src, len(self.scope)))
        self.src = ""

    def __insertStatement(self, pc: int) -> None:
        # insert current statement into lines at pc location
        for i in range(len(self.lines)):
            if self.lines[i].startPC <= pc and self.lines[i].endPC >= pc:
                self.lines.insert(i, _Line(pc, pc, self.src, self.lines[i-1].scope if i > 0 else 0))
                self.src = ""
                return i

        self.src = ""

    # walks traceback, if local wasn't set before, the local needs to be defined
    def __needsDefined(self, reg) -> bool:
        for _, trace in self.traceback.items():
            if reg in trace.sets:
                return False

        # wasn't set in traceback! needs defined!
        return True

    def __loadLocals(self):
        for i in range(len(self.chunk.locals)):
            name = self.chunk.locals[i].name
            if isValidLocal(name):
                self.locals[i] = name
            elif "(for " not in name: # if it's a for loop register, ignore
                self.__makeLocalIdentifier(i)

    # when you *know* the register *has* to be a local (for loops, etc.)
    def __getLocal(self, indx: int) -> str:
        return self.locals[indx] if indx in self.locals else self.__makeLocalIdentifier(indx)

    def __getReg(self, indx: int) -> str:
        self.__addUseTraceback(indx)
        if indx in self.locals:
            return self.locals[indx]
        elif indx in self.top:
            return self.top[indx]
        else:
            # Handle the case where the register hasn't been initialized
            # You might want to return a default value or raise a more informative error
            return f"R[{indx}]"  # or whatever makes sense in your context
    def __setReg(self, indx: int, code: str, forceLocal: bool = False) -> None:
        if indx not in self.variable_usage:
            self.variable_usage[indx] = {'first_use': self.pc, 'last_use': self.pc}
        else:
            self.variable_usage[indx]['last_use'] = self.pc
        # if the top indx is a local, set it
        if indx in self.locals:
            if self.__needsDefined(indx):
                self.__newLocal(indx, code)
            else:
                self.__addExpr(self.locals[indx] + " = " + code)
                self.__endStatement()
        elif self.aggressiveLocals or forceLocal: # 'every register is a local!!'
            self.__newLocal(indx, code)

        self.__addSetTraceback(indx)
        self.top[indx] = code
    def __optimize_variable_scopes(self):
        for var, usage in self.variable_usage.items():
            if var in self.locals:
                local_name = self.locals[var]
                start_pc = usage['first_use']
                end_pc = usage['last_use']
                
                # Find the appropriate scope for this variable
                scope_level = 0
                for block in self.blocks:
                    if start_pc >= block[0][0] and end_pc <= block[-1][0]:
                        break
                    scope_level += 1
                
                # Update the local's scope
                for i, line in enumerate(self.lines):
                    if line.startPC <= start_pc and line.endPC >= end_pc:
                        if "local " + local_name in line.src:
                            self.lines[i].scope = scope_level
                            break
    # ========================================[[ Locals ]]=========================================

    def __makeLocalIdentifier(self, indx: int) -> str:
        # first, check if we have a local name already determined
        if indx in self.locals:
            return self.locals[indx]

        # otherwise, generate a local
        self.locals[indx] = "__unknLocal%d" % self.unknownLocalCount
        self.unknownLocalCount += 1

        return self.locals[indx]

    def __newLocal(self, indx: int, expr: str) -> None:
        self.__makeLocalIdentifier(indx)

        self.__addExpr("local " + self.locals[indx] + " = " + expr)
        self.__endStatement()

    # ========================================[[ Scopes ]]=========================================

    def __startScope(self, scopeType: str, start: int, size: int) -> None:
        self.__addExpr(scopeType)
        self.__endStatement()
        self.scope.append(_Scope(start, start + size))

        # checks if we need to end a scope
    def __checkScope(self) -> None:
        if self.scope and self.pc > self.scope[-1].endPC:
            self.__endScope()

    def __endScope(self) -> None:
        if self.scope:  # Only proceed if there are scopes to end
            self.__endStatement()
            self.__addExpr("end")
            self.scope.pop()
            self.__endStatement()
        else:
            # Optionally, you can add a warning or debug message here
            print("Warning: Attempted to end scope when no scopes were left.")
    # =====================================[[ Instructions ]]======================================

    def __emitOperand(self, a: int, b: str, c: str, op: str) -> None:
        self.__setReg(a, "(" + b + op + c + ")")

    # handles conditional jumps
    def __condJmp(self, op: str, rkBC: bool = True):
        instr = self.__getCurrInstr()
        jmpType = "if"
        scopeStart = "then"

        # we need to check if the jmp location has a jump back (if so, it's a while loop)
        jmp = self.__getNextInstr().B + 1
        jmpToInstr = self.__getInstrAtPC(self.pc + jmp)

        if jmpToInstr.opcode == Opcodes.JMP:
            # if this jump jumps back to this compJmp, it's a loop!
            if self.pc + jmp + jmpToInstr.B <= self.pc + 1:
                jmpType = "while"
                scopeStart = "do"
        elif jmp < 0:
            # 'repeat until' loop (probably)
            jmpType = "until"
            scopeStart = None

        if instr.A > 0:
            self.__addExpr("%s not " % jmpType)
        else:
            self.__addExpr("%s " % jmpType)

        # write actual comparison
        if rkBC:
            self.__addExpr(self.__readRK(instr.B) + op + self.__readRK(instr.C) + " ")
        else: # just testing rkB
            self.__addExpr(op + self.__readRK(instr.B))

        self.pc += 1 # skip next instr
        if scopeStart:
            self.__startScope("%s " % scopeStart, self.pc - 1, jmp)

            # we end the statement *after* scopeStart
            self.__endStatement()
        else:
            # end the statement prior to repeat
            self.__endStatement()

            # it's a repeat until loop, insert 'repeat' at the jumpTo location
            self.__addExpr("repeat")
            insertedLine = self.__insertStatement(self.pc + jmp)

            # add scope to every line in-between
            for i in range(insertedLine+1, len(self.lines)-1):
                self.lines[i].scope += 1

    # 'RK's are special in because can be a register or a konstant. a bitflag is read to determine which
    def __readRK(self, rk: int) -> str:
        if (whichRK(rk)) > 0:
            return self.chunk.getConstant(readRKasK(rk)).toCode()
        else:
            return self.__getReg(rk)

    # walk & peak ahead NEWTABLE
    def __parseNewTable(self, indx: int):
        # TODO: parse SETTABLE too?
        tblOps = [Opcodes.LOADK, Opcodes.SETLIST]

        instr = self.__getNextInstr()
        cachedRegs = {}
        tbl = "{"
        while instr.opcode in tblOps:
            if instr.opcode == Opcodes.LOADK: # operate on registers
                cachedRegs[instr.A] = self.chunk.getConstant(instr.B).toCode()
            elif instr.opcode == Opcodes.SETLIST:
                numElems = instr.B

                for i in range(numElems):
                    tbl += "%s, " % cachedRegs[instr.A + i + 1]
                    del cachedRegs[instr.A + i + 1]

            self.pc += 1
            instr = self.__getNextInstr()
        tbl += "}"

        # i use forceLocal here even though i don't know *for sure* that the register is a local.
        # this does help later though if the table is reused (which is 99% of the time). the other 1%
        # only affects syntax and may look a little weird but is fine and equivalent non-the-less
        self.__setReg(indx, tbl, forceLocal=True)
        self.__endStatement()

        # if we have leftovers... oops, set those
        for i, v in cachedRegs.items():
            self.__setReg(i, v)

    def parseInstr(self):
        if not hasattr(self, 'blocks'):
            self.__analyze_control_flow()
        
        instr = self.__getCurrInstr()
        
        match instr.opcode:
            case Opcodes.MOVE: # move is a fake ABC instr, C is ignored
                # move registers
                self.__setReg(instr.A, self.__getReg(instr.B))
            case Opcodes.LOADK:
                const = self.chunk.getConstant(instr.B)
                self.__setReg(instr.A, const.toCode())
                self.__set_inferred_type(instr.A, const.type.name.lower())
            case Opcodes.SELF:
                # SELF is used for method calls (obj:method())
                # A is the register where the function will be stored
                # B is the register containing the table (object)
                # C is the index of the method name (usually a constant)
                obj = self.__getReg(instr.B)
                method = self.__readRK(instr.C)
                self.__setReg(instr.A, f"{obj}:{method}")
                self.__setReg(instr.A + 1, obj)  # 'self' parameter
            case Opcodes.TAILCALL:
                callStr = f"{self.__getReg(instr.A)}("
                for i in range(instr.A + 1, instr.A + instr.B - 1):
                    callStr += f"{self.__getReg(i)}, "
                callStr = callStr.rstrip(", ") + ")"
                self.__addExpr(f"return {callStr}")
                self.__endStatement()
            case Opcodes.SETUPVAL:
                self.__addExpr(f"upvalue[{instr.B}] = {self.__getReg(instr.A)}")
                self.__endStatement()
            case Opcodes.NEWTABLE:
                self.__parseNewTable(instr.A)
                self.__add_comment(f"Created new table in R[{instr.A}] with {instr.B} array elements and {instr.C} hash elements")
            case Opcodes.VARARG:
                # VARARG handles variable arguments
                # A is the register where to store the args
                # B is the number of args wanted (0 means all)
                if instr.B == 0:
                    # If B is 0, it means "all remaining arguments"
                    self.__setReg(instr.A, "...")
                elif instr.B == 1:
                    # If B is 1, it means "only one argument"
                    self.__setReg(instr.A, "select(1, ...)")
                else:
                    # If B > 1, it means "B-1 arguments"
                    args = ", ".join(f"select({i}, ...)" for i in range(1, instr.B))
                    self.__setReg(instr.A, args)
                self.__endStatement()
            case Opcodes.CLOSE:
                # CLOSE is used to close upvalues
                # A is the register up to which upvalues should be closed
                self.__addExpr(f"-- close upvalues up to R[{instr.A}]")
                self.__endStatement()
            case Opcodes.TFORLOOP:
                # TFORLOOP is used in generic for loops
                # A is the base register of the loop
                # C is the number of return values
                self.__addExpr("for ")
                for i in range(instr.C):
                    self.__addExpr(self.__getLocal(instr.A + 2 + i))
                    if i < instr.C - 1:
                        self.__addExpr(", ")
                self.__addExpr(" in ")
                self.__addExpr(self.__getReg(instr.A))
                self.__startScope(" do", self.pc, instr.B)
            case Opcodes.LOADNIL:
                # LOADNIL sets a range of registers to nil
                # A is the first register to set to nil
                # B is the last register to set to nil (inclusive)
                for i in range(instr.A, instr.B + 1):
                    self.__setReg(i, "nil")
                self.__endStatement()
            case Opcodes.TESTSET:
                # TESTSET is used for conditional assignments
                # A is the register to set if the test succeeds
                # B is the register to test
                # C is the condition (0 = false, 1 = true)
                condition = "not " if instr.C == 0 else ""
                test_value = self.__getReg(instr.B)
                self.__addExpr(f"if {condition}{test_value} then")
                self.__setReg(instr.A, test_value)
                self.__endStatement()
                self.__startScope("", self.pc, 1)  # Start a new scope for the conditional block
            case Opcodes.LOADBOOL:
                if instr.B == 0:
                    self.__setReg(instr.A, "false")
                else:
                    self.__setReg(instr.A, "true")
            case Opcodes.GETGLOBAL:
                self.__setReg(instr.A, self.chunk.getConstant(instr.B).data)
            case Opcodes.GETTABLE:
                self.__setReg(instr.A, self.__getReg(instr.B) + "[" + self.__readRK(instr.C) + "]")
            case Opcodes.SETGLOBAL:
                self.__addExpr(self.chunk.getConstant(instr.B).data + " = " + self.__getReg(instr.A))
                self.__endStatement()
            case Opcodes.SETTABLE:
                self.__addExpr(self.__getReg(instr.A) + "[" + self.__readRK(instr.B) + "] = " + self.__readRK(instr.C))
                self.__endStatement()
            case Opcodes.ADD:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " + ")
            case Opcodes.SUB:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " - ")
            case Opcodes.MUL:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " * ")
            case Opcodes.DIV:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " / ")
            case Opcodes.MOD:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " % ")
            case Opcodes.POW:
                self.__emitOperand(instr.A, self.__readRK(instr.B), self.__readRK(instr.C), " ^ ")
            case Opcodes.UNM:
                self.__setReg(instr.A, "-" + self.__getReg(instr.B))
            case Opcodes.NOT:
                self.__setReg(instr.A, "not " + self.__getReg(instr.B))
            case Opcodes.LEN:
                self.__setReg(instr.A, "#" + self.__getReg(instr.B))
            case Opcodes.CONCAT:
                count = instr.C-instr.B+1
                concatStr = ""

                # concat all items on stack from RC to RB
                for i in range(count):
                    concatStr += self.__getReg(instr.B + i) + (" .. " if not i == count - 1 else "")

                self.__setReg(instr.A, concatStr)
            case Opcodes.JMP:
                pass
            case Opcodes.EQ:
                self.__condJmp(" == ")
            case Opcodes.LT:
                self.__condJmp(" < ")
            case Opcodes.LE:
                self.__condJmp(" <= ")
            case Opcodes.TEST:
                if instr.C == 0:
                    self.__condJmp("", False)
                else:
                    self.__condJmp("not ", False)
            case Opcodes.CALL:
                func_name = self.__getReg(instr.A)
                if func_name in LUA_STDLIB:
                    module = LUA_STDLIB[func_name]
                    if module != "global":
                        func_name = f"{module}.{func_name.split('.')[-1]}"
                    self.__add_comment(f"Calling Lua standard library function: {func_name}")
                
                preStr = ""
                callStr = f"{func_name}("
                
                # parse arguments
                for i in range(instr.A + 1, instr.A + instr.B):
                    callStr += f"{self.__getReg(i)}, "
                callStr = callStr.rstrip(", ") + ")"

                # parse return values
                if instr.C > 1:
                    preStr = "local "
                    for indx in range(instr.A, instr.A + instr.C - 1):
                        if indx in self.locals:
                            ident = self.locals[indx]
                        else:
                            ident = self.__makeLocalIdentifier(indx)
                        preStr += ident
                        self.top[indx] = ident
                        preStr += ", " if not indx == instr.A + instr.C - 2 else ""
                    preStr += " = "

                self.__addExpr(preStr + callStr)
                self.__endStatement()
           
            case Opcodes.RETURN:
                returnStr = "return "
                if instr.B == 0:
                    returnStr += "..."  # Return all results from top
                elif instr.B > 1:
                    for i in range(instr.A, instr.A + instr.B - 1):
                        returnStr += f"{self.__getReg(i)}, "
                    returnStr = returnStr.rstrip(", ")
                elif instr.B == 1:
                    returnStr += self.__getReg(instr.A)
                self.__addExpr(returnStr)
                self.__endStatement()
            case Opcodes.FORLOOP:
                # This is the loop back point, so we just need to end the scope
                self.__endScope()
            case Opcodes.TFORLOOP:
                # The actual loop body is handled by the previous TFORPREP
                # Here we just need to check if we should continue the loop
                self.__addExpr(f"if {self.__getReg(instr.A + 3)} ~= nil then")
                self.__setReg(instr.A + 2, self.__getReg(instr.A + 3))
                self.__endStatement()
                self.__addExpr("else")
                self.__endStatement()
                self.__addExpr("  break")
                self.__endStatement()
                self.__addExpr("end")
                self.__endStatement()
            case Opcodes.VARARG:
                if instr.B == 0:
                    self.__setReg(instr.A, "...")
                elif instr.B == 1:
                    self.__setReg(instr.A, "select(1, ...)")
                else:
                    args = ", ".join(f"select({i}, ...)" for i in range(1, instr.B))
                    self.__setReg(instr.A, f"{{{args}}}")
                self.__endStatement()
            case Opcodes.FORPREP:
                self.__addExpr("for %s = %s, %s, %s " % (self.__getLocal(instr.A+3), self.__getReg(instr.A), self.__getReg(instr.A + 1), self.__getReg(instr.A + 2)))
                self.__startScope("do", self.pc, instr.B)
            case Opcodes.SETLIST:
                # LFIELDS_PER_FLUSH (50) is the number of elements that *should* have been set in the list in the *last* SETLIST
                # eg.
                # [ 49]      LOADK :  R[49]   K[1]               ; load 0.0 into R[49]
                # [ 50]      LOADK :  R[50]   K[1]               ; load 0.0 into R[50]
                # [ 51]    SETLIST :      0     50      1        ; sets list[1..50]
                # [ 52]      LOADK :   R[1]   K[1]               ; load 0.0 into R[1]
                # [ 53]    SETLIST :      0      1      2        ; sets list[51..51]
                numElems = instr.B
                startAt = ((instr.C - 1) * 50)
                ident = self.__getLocal(instr.A)

                # set each index (TODO: make tables less verbose)
                for i in range(numElems):
                    self.__addExpr("%s[%d] = %s" % (ident, (startAt + i + 1), self.__getReg(instr.A + i + 1)))
                    self.__endStatement()
            case Opcodes.CLOSURE:
                proto = LuaDecomp(self.chunk.protos[instr.B], headChunk=False, scopeOffset=len(self.scope))
                self.__setReg(instr.A, proto.getPseudoCode())
            case Opcodes.GETUPVAL:
                # Upvalue is retrieved and assigned to a register
                self.__setReg(instr.A, "upvalue[" + str(instr.B) + "]")
            case _:
                raise Exception("unsupported instruction: %s" % instr.toString())