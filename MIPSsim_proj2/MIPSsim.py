#!usr/bin/env python
# -*- coding:utf-8 -*-
import sys
import getopt
from functools import reduce
import Queue  # python2

# 三种指令类型字典
category1 = {'000': 'J', '010': 'BEQ', '100': 'BGTZ', '101': 'BREAK', '110': 'SW', '111': 'LW'}
category2 = {'000': 'ADD', '001': 'SUB', '010': 'MUL', '011': 'AND', '100': 'OR', '101': 'XOR', '110': 'NOR'}
category3 = {'000': 'ADDI', '001': 'ANDI', '010': 'ORI', '011': 'XORI'}

proj_path = str(sys.path[0])
# print proj_path


# MIPS模拟器
def simulator(sample_path):
    fr = open(sample_path, 'r')
    cont = [inst.strip() for inst in fr.readlines()]  # 处理文档
    contSize = len(cont)
    # 记录BREAK指令位置 axis前为指令 axis后为数据
    for i in range(contSize):
        if cont[i][3:6] == '101':  axis = i + 1

    '''添加每条对应地址'''
    addr = 128  # 起始指令地址
    l = [cont[i] + '\t' + str(addr + i * 4) for i in range(contSize)]  # 添加对应地址

    '''分别解析指令和数据'''
    instructions = [ins_decode(tl, 1) for tl in l[0:axis]]  # axis前为指令 指令解析
    # print(instructions)
    data = [data_decode(tl) for tl in l[axis:]]  # axis后为数据 数据解析
    # print(data)

    disassembly = instructions + data  # 反汇编结果
    disassembly[-1] = disassembly[-1].strip()  # 把disassembly里(data后面)多出的最后一行空格去掉

    '''指令部分和数据部分预处理'''
    # dataSegmDict:{地址:值}
    # insSegmDict:{'instr地址':instruction, 地址: 32位指令}
    merge_dict = lambda x, y: dict(x, **y)  # 将两个字典合并
    insSegmDict = reduce(merge_dict, map(ins_to_dict, instructions))  # 将所有字典合并
    dataSegmDict = reduce(merge_dict, map(data_to_dict, l[axis:]))

    '''将模拟结果simulation_trace_list写入文件'''
    with open(proj_path + '/generated_simulation.txt', 'w') as f:
        f.writelines(sim_execute(dataSegmDict, insSegmDict))


# MIPS模拟器执行指令
def sim_execute(dataSegmDict, insSegmDict):
    PC = 128  # 记录下一个需提取的指令的地址 初始值为128
    NPC = 0
    isUpdatePC = False  # 是否更新PC

    waiting_brInstr = ''
    exe_brInstr = ''
    preIssue = [''] * 4
    preALU = [''] * 2
    preMEM, postALU, postMEM = '', '', ''
    preIssueQueue = Queue.Queue(maxsize=4)  # Constructor for a FIFO queue
    preALUQueue = Queue.Queue(maxsize=2)

    preALULen, preIssueLen = 0, 0  # 上一个ALU、Issue里entry被占个数

    # baseLW = registers[int(base, 2)]
    # rtLW, offsetLW = int(rt, 2), int(offset, 2)
    baseLW, rtLW, offsetLW, baseSW, rtSW, offsetSW = '', '', '', '', '', ''
    baseLWTemp, rtLWTemp, offsetLWTemp, baseSWTemp, rtSWTemp, offsetSWTemp = '', '', '', '', '', ''

    registers, regStatus, preRegStatus = [0] * 32, [0] * 32, [0] * 32   # status 初始值为0  2为写入

    dataSortedList = sorted(dataSegmDict.keys())  # dataSegmDict:{地址:值}  按地址排序
    simulation_trace_list = []
    value = 1  # Cycle[value]
    isExecute = True

    insLen = len(insSegmDict) / 2
    dataLen = len(dataSegmDict)
    firstDataAddress = PC + 4 * insLen
    ninthDataAddress = firstDataAddress + 4 * 8

    while (isExecute):
        '''WB Unit: 一个cycle可最多执行两个写回: postALU 、 postMEM( LW )'''
        # The update is finished before the end of the cycle.
        # The new value will be available at the beginning of next cycle.
        if postALU != '':  # any instruction except LW or SW
            registers, dataSegmDict = instr_execute(postALU, registers, dataSegmDict)  # 执行指令。改变 Register、Data 对应值

            regStatus = reset_instr_regStatus(postALU, regStatus)  # postALU -> 0
            postALU = ''  # 执行完  postALU ready

        if postMEM != '':  # LW   memory[base+offset] -> rt
            registers[rtLW] = dataSegmDict[str(baseLW + offsetLW)]    # 把值存进rtLW寄存器
            rtLW, baseLW, offsetLW = rtLWTemp, baseLWTemp, offsetLWTemp
            rtLWTemp, baseLWTemp, offsetLWTemp = '', '', ''

            base, rt = postMEM[6:11], postMEM[11:16]
            regStatus[int(rt, 2)], preRegStatus[int(base, 2)] = 0, 0  # 已经Load到rt,将rt状态设为0
            postMEM = ''  # postMEM ready

        '''MEM Unit: 处理LW、SW命令'''
        if preMEM != '':  # reads from Pre-MEM queue
            instrInMEM = ins_decode(preMEM, 2)[1:3]  # LW, SW
            # print(ins_decode(preMEM, 2))   # [LW R3, 184(R6)]
            if instrInMEM == 'LW':
                postMEM = preMEM   # preMEM -> postMEM
                preMEM = ''  # preMEM ready

            if instrInMEM == 'SW':     # When a SW instruction finishes, nothing would be sent to Post-MEM queue.
                dataSegmDict[str(baseSW + offsetSW)] = rtSW    # 改变数据区对应的值
                rtSW, baseSW, offsetSW = rtSWTemp, baseSWTemp, offsetSWTemp
                rtSWTemp, baseSWTemp, offsetSWTemp = '', '', ''
                preMEM = ''  # preMEM ready

        '''ALU Unit: 处理memory(LW、SW) instructions和所有non-memory instructions'''
        # fetch one instruction each cycle from the Pre-ALU queue
        # MEM( or WB) is guaranteed to consume(remove) the entry from the Post-MEM( or Post-ALU) queue
        # before the end of the current cycle.
        if preALUQueue.qsize() != 0:
            insPreALU = preALUQueue.get()
            instr = ins_decode(insPreALU, 2)[1:3]  # 根据指令判断

            # remove and compute
            if instr in ['LW', 'SW']:
                preMEM = insPreALU    # preALU -> preMEM
                base, rt, offset = insPreALU[6:11], insPreALU[11:16], insPreALU[16:32]

                if instr == 'LW':
                    if baseLW == '':
                        baseLW = registers[int(base, 2)]
                        rtLW, offsetLW = int(rt, 2), int(offset, 2)
                    else:
                        baseLWTemp = registers[int(base, 2)]
                        rtLWTemp, offsetLWTemp = int(rt, 2), int(offset, 2)
                    regStatus[int(base, 2)], preRegStatus[int(base, 2)] = 0, 0

                else:
                    if baseSW == '':
                        baseSW, rtSW = registers[int(base, 2)], registers[int(rt, 2)]
                        offsetSW = int(offset, 2)
                    else:
                        baseSWTemp, rtSWTemp = registers[int(base, 2)], registers[int(rt, 2)]
                        offsetSWTemp = int(offset, 2)
                    regStatus[int(base, 2)], preRegStatus[int(base, 2)] = 0, 0
                    regStatus[int(rt, 2)], preRegStatus[int(rt, 2)] = 0, 0
            else:
                postALU = insPreALU  # preALU --> postALU

        '''Issue Unit: 从Register File读操作数, 当所有源操作数都ready的时候issue指令'''
        regStatusCopy, issueRegStatus = preRegStatus, preRegStatus
        # 每个cycle可乱序issue至多两条指令
        if not preIssueQueue.empty():
            queueTemp = Queue.Queue(maxsize=4)
            count, swCount, lwCount = 0, 0, 0
            # 根据Pre-ALU内entry被占个数来issue指令
            # No structural hazards    Pre-ALU has empty slots at the end of last cycle.
            if preALULen == 0:
                while not preIssueQueue.empty():
                    insPreIssue = preIssueQueue.get()
                    instr = ins_decode(insPreIssue, 1)[0:2]  # 当前preIssue里指令
                    if is_insExecutable(insPreIssue, regStatusCopy) and count != 2:   # 最多issue两条指令
                        # 防止访问内存时的数据冒险
                        if (instr == 'SW' and swCount != 0 and lwCount != 0) or (instr == 'LW' and swCount != 0):
                            regStatusCopy = update_regStatus(insPreIssue, regStatusCopy)
                            queueTemp.put(insPreIssue)
                            if instr == 'SW':  swCount += 1
                            if instr == 'LW':  lwCount += 1
                        else:
                            regStatus = update_regStatus(insPreIssue, regStatus)
                            issueRegStatus = update_regStatus(insPreIssue, preRegStatus)
                            regStatusCopy = update_regStatus(insPreIssue, regStatusCopy)  # 防止发射的两条指令之间有数据冒险
                            preALUQueue.put(insPreIssue)
                            count += 1
                    else:
                        regStatusCopy = update_regStatus(insPreIssue, regStatusCopy)
                        queueTemp.put(insPreIssue)
                        if instr == 'SW':  swCount += 1
                        if instr == 'LW':  lwCount += 1
                preIssueQueue = queueTemp

            elif preALULen == 1:  # 可issue一条指令
                while not preIssueQueue.empty():
                    insPreIssue = preIssueQueue.get()
                    instr = ins_decode(insPreIssue, 1)[0:2]
                    if is_insExecutable(insPreIssue, regStatusCopy) and count == 0:
                        # 防止访问内存时的数据冒险
                        if (instr == 'SW' and swCount != 0 and lwCount != 0) or (instr == 'LW' and swCount != 0):
                            regStatusCopy = update_regStatus(insPreIssue, regStatusCopy)
                            queueTemp.put(insPreIssue)
                            if instr == 'SW':  swCount += 1
                            if instr == 'LW':  lwCount += 1
                        else:
                            regStatus = update_regStatus(insPreIssue, regStatus)
                            issueRegStatus = update_regStatus(insPreIssue, preRegStatus)
                            preALUQueue.put(insPreIssue)
                            count += 1
                    else:
                        regStatusCopy = update_regStatus(insPreIssue, regStatusCopy)
                        queueTemp.put(insPreIssue)
                        if instr == 'SW':  swCount += 1
                        if instr == 'LW':  lwCount += 1
                preIssueQueue = queueTemp

        regStatusCopy = issueRegStatus

        '''IF Unit:  每个cycle至多fetch和decode两条指令'''
        if exe_brInstr != '':  exe_brInstr = ''  # 发射指令
        if waiting_brInstr == '':
            if preIssueLen < 3:    # 可以加载两条
                # insSegmDict: {'instr地址':instruction, 地址: 32位指令}
                if (insSegmDict[str(PC)])[3:6] in ['010', '100']:  # BREAK  BGTZ
                    NPC = PC + 4
                    isUpdatePC = True
                    preIssueQueue.put(insSegmDict[str(PC)])
                    PC += 4
                else:
                    preIssueQueue.put(insSegmDict[str(PC)])
                    PC += 4
                if PC < int(dataSortedList[0]):
                    preIssueQueue.put(insSegmDict[str(PC)])
                    PC += 4
            elif preIssueLen == 3:  # 可以加载一条
                preIssueQueue.put(insSegmDict[str(PC)])
                PC += 4
            else:  # 队列已满，防止结构冒险
                pass

            queueTemp = preIssueQueue
            preIssueQueue = Queue.Queue(maxsize=4)


            while(not queueTemp.empty()):
                instr = queueTemp.get()
                if instr[0:3] == '000':
                    opcode1, rs1, rt1 = instr[3:6], instr[6:11], instr[11:16]
                    # J | instr_index(26)
                    # BEQ | rs(5) | rt(5) | offset(16)     if rs = rt then branch
                    # BGTZ | rs(5) | 00000 | offset(16)    if rs > 0 then branch
                    jAddr = instr[6:32]  # J指令跳转地址
                    offset = instr[16:32]  # 跳转偏移量

                    if category1[opcode1] == 'J':
                        PC = int(jAddr, 2) * 4
                        exe_brInstr = instr

                    elif category1[opcode1] == 'BEQ':
                        if regStatusCopy[int(rs1, 2)] != 2 and regStatusCopy[int(rt1, 2)] != 2:
                            if registers[int(rs1, 2)] == registers[int(rt1, 2)]:
                                PC += int(offset, 2) * 4
                            exe_brInstr = instr
                        else:
                            waiting_brInstr = instr
                            if isUpdatePC:
                                PC = NPC
                                isUpdatePC = False
                            break

                    elif category1[opcode1] == 'BGTZ':
                        if regStatusCopy[int(rs1, 2)] != 2:
                            if registers[int(rs1, 2)] > 0:
                                PC += int(offset, 2) * 4
                            exe_brInstr = instr
                        else:
                            waiting_brInstr = instr
                            if isUpdatePC:
                                PC = NPC
                                isUpdatePC = False
                            break

                    elif category1[opcode1] == 'BREAK':
                        isExecute = False
                        exe_brInstr = instr

                    else:
                        regStatusCopy = update_regStatus(instr, regStatusCopy)
                        preIssueQueue.put(instr)
                else:
                    regStatusCopy = update_regStatus(instr, regStatusCopy)
                    preIssueQueue.put(instr)

        else:         # waiting_brInstr != ''
            queueTemp = preIssueQueue
            preIssueQueue = Queue.Queue(maxsize=4)
            while(not queueTemp.empty()):
                instr = queueTemp.get()
                regStatusCopy = update_regStatus(instr, regStatusCopy)
                preIssueQueue._put(instr)

            instr = waiting_brInstr
            opcode1, rs1, rt1, offset = instr[3:6], instr[6:11], instr[11:16], instr[16:32]
            # BEQ | rs(5) | rt(5) | offset(16)     if rs = rt then branch
            # BGTZ | rs(5) | 00000 | offset(16)    if rs > 0 then branch
            if category1[opcode1] == 'BEQ':
                if regStatusCopy[int(rs1, 2)] != 2 and regStatusCopy[int(rt1, 2)] != 2:
                    if registers[int(rs1, 2)] == registers[int(rt1, 2)]:
                        PC += int(offset, 2) * 4
                    exe_brInstr = instr
                    waiting_brInstr = ''

            if category1[opcode1] == 'BGTZ':
                if regStatusCopy[int(rs1, 2)] != 2:
                    if registers[int(rs1, 2)] > 0:
                        PC += int(offset, 2) * 4
                    exe_brInstr = instr
                    waiting_brInstr = ''

        preRegStatus = []
        for n in regStatus:
            preRegStatus.append(n)  # 该cycle最终寄存器状态

        '''输出结果'''
        queueIssue = Queue.Queue(maxsize=4)
        queueALU = Queue.Queue(maxsize=2)

        for index in range(4):
            if preIssueQueue.qsize() != 0:
                ins = preIssueQueue.get()
                queueIssue.put(ins)
                preIssue[index] = str(ins_decode(ins, 2))
            else:
                preIssue[index] = ''

        for index in range(2):
            if preALUQueue.qsize() != 0:
                ins = preALUQueue.get()
                queueALU.put(ins)
                preALU[index] = str(ins_decode(ins, 2))
            else:
                preALU[index] = ''

        # 为下一个cycle更新preIssueQueue, preALUQueue 和 preIssueLen preALULen 大小
        preIssueQueue, preALUQueue = queueIssue, queueALU
        preIssueLen, preALULen = queueIssue.qsize(), queueALU.qsize()

        ll = '--------------------\nCycle:' + str(value) + '\n\n' + 'IF Unit:\n'
        ll += '\tWaiting Instruction:' + ins_decode(waiting_brInstr, 2) + '\n\tExecuted Instruction:' + ins_decode(
            exe_brInstr, 2)
        ll += '\nPre-Issue Queue:\n\t' + 'Entry 0:' + preIssue[0] + '\n\tEntry 1:' + preIssue[1] + '\n\tEntry 2:' + \
              preIssue[2] + '\n\tEntry 3:' + preIssue[3]
        ll += '\nPre-ALU Queue:\n\t' + 'Entry 0:' + preALU[0] + '\n\tEntry 1:' + preALU[1]
        ll += '\nPre-MEM Queue:' + ins_decode(preMEM, 2)
        ll += '\nPost-MEM Queue:' + ins_decode(postMEM, 2)
        ll += '\nPost-ALU Queue:' + ins_decode(postALU, 2)

        ll += '\n\nRegisters\nR00:'
        for x in registers[0:8]: ll += '\t' + str(x)
        ll += '\nR08:'
        for x in registers[8:16]: ll += '\t' + str(x)
        ll += '\nR16:'
        for x in registers[16:24]: ll += '\t' + str(x)
        ll += '\nR24:'
        for x in registers[24:]: ll += '\t' + str(x)

        ll += '\n\nData\n' + str(firstDataAddress) + ':'
        for x in dataSortedList[0:8]: ll += '\t' + str(dataSegmDict[x])
        if dataLen > 8:
            ll += '\n' + str(ninthDataAddress) + ':'
            for x in dataSortedList[8:16]: ll += '\t' + str(dataSegmDict[x])
        ll += '\n'

        simulation_trace_list.append(ll)
        value += 1

    return simulation_trace_list


# 更新寄存器状态
def update_regStatus(instr, regStatus):
    leftmost = instr[0:3]
    if leftmost == '000':
        opcode1, base, rt1 = instr[3:6], instr[6:11], instr[11:16]
        # SW | base(5) | rt(5) | offset(16)     memory[base+offset] ← rt
        # LW | base(5) | rt(5) | offset(16)     rt ← memory[base+offset]
        if category1[opcode1] == 'SW':
            if regStatus[int(base, 2)] == 0:
                regStatus[int(base, 2)] = 1
            if regStatus[int(rt1, 2)] == 0:
                regStatus[int(rt1, 2)] = 1

        if category1[opcode1] == 'LW':
            if regStatus[int(base, 2)] == 0:
                regStatus[int(base, 2)] = 1
            regStatus[int(rt1, 2)] = 2

    if leftmost == '110':
        # 110 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | rd(5 bits) | 00000000000
        # rd ← rs (ins) rt
        rs2, rt2, rd2 = instr[3:8], instr[8:13], instr[16:21]
        if regStatus[int(rs2, 2)] == 0:
            regStatus[int(rs2, 2)] = 1
        if regStatus[int(rt2, 2)] == 0:
            regStatus[int(rt2, 2)] = 1
        regStatus[int(rd2, 2)] = 2

    if leftmost == '111':
        # 111 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | immediate_value(16 bits)
        # rt ← rs (ins) immediate
        rs3, rt3 = instr[3:8], instr[8:13]
        if regStatus[int(rs3, 2)] == 0:
            regStatus[int(rs3, 2)] = 1
        regStatus[int(rt3, 2)] = 2

    return regStatus


# 重置寄存器状态
def reset_instr_regStatus(instr, regStatus):
    leftmost = instr[0:3]
    if leftmost == '000':
        base, rt1 = instr[6:11], instr[11:16]
        regStatus[int(base, 2)], regStatus[int(rt1, 2)] = 0, 0

    if leftmost == '110':
        rs2, rt2, rd2 = instr[3:8], instr[8:13], instr[16:21]
        regStatus[int(rs2, 2)], regStatus[int(rt2, 2)], regStatus[int(rd2, 2)] = 0, 0, 0

    if leftmost == '111':
        rs3, rt3 = instr[3:8], instr[8:13]
        regStatus[int(rs3, 2)], regStatus[int(rt3, 2)] = 0, 0
    return regStatus


# 指令是否能执行
def is_insExecutable(instr, regStatus):
    leftmost = instr[0:3]
    if leftmost == '000':
        opcode1, base, rt1 = instr[3:6], instr[6:11], instr[11:16]
        # SW | base(5) | rt(5) | offset(16)     memory[base+offset] ← rt
        # LW | base(5) | rt(5) | offset(16)     rt ← memory[base+offset]
        if category1[opcode1] == 'SW':
            if regStatus[int(base, 2)] == 2 or regStatus[int(rt1, 2)] == 2:
                return False
        if category1[opcode1] == 'LW':
            if regStatus[int(base, 2)] == 2 or regStatus[int(rt1, 2)] != 0:
                return False

    if leftmost == '110':
        # 110 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | rd(5 bits) | 00000000000
        # rd ← rs (ins) rt
        rs2, rt2, rd2 = instr[3:8], instr[8:13], instr[16:21]
        if regStatus[int(rs2, 2)] == 2 or regStatus[int(rt2, 2)] == 2 or regStatus[int(rd2, 2)] != 0:
            return False

    if leftmost == '111':
        # 111 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | immediate_value(16 bits)
        # rt ← rs (ins) immediate
        rs3, rt3 = instr[3:8], instr[8:13]
        if regStatus[int(rs3, 2)] == 2 or regStatus[int(rt3, 2)] != 0:
            return False

    return True


# 执行指令
def instr_execute(instr, registers, dataSegmDict):
    leftmost = instr[0:3]
    if leftmost == '000':
        # 000 | opcode(3 bits) | Same as MIPS instruction
        opcode1, base, rt1, offset = instr[3:6], instr[6:11], instr[11:16], instr[16:32]
        # SW | base(5) | rt(5) | offset(16)     memory[base+offset] ← rt
        # LW | base(5) | rt(5) | offset(16)     rt ← memory[base+offset]

        if category1[opcode1] == 'SW':
            try:
                # 把寄存器的值存到对应的地址内
                dataSegmDict[str(registers[int(base, 2)] + int(offset, 2))] = registers[int(rt1, 2)]
            except:
                pass
        if category1[opcode1] == 'LW':
            try:
                # 改变寄存器内的值
                registers[int(rt1, 2)] = dataSegmDict[str(registers[int(base, 2)] + int(offset, 2))]
            except:
                pass

    if leftmost == '110':
        # 110 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | rd(5 bits) | 00000000000
        # rd ← rs (ins) rt
        rs2, rt2, opcode2, rd2 = instr[3:8], instr[8:13], instr[13:16], instr[16:21]
        if category2[opcode2] == 'ADD':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] + registers[int(rt2, 2)]
        if category2[opcode2] == 'SUB':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] - registers[int(rt2, 2)]
        if category2[opcode2] == 'MUL':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] * registers[int(rt2, 2)]
        if category2[opcode2] == 'AND':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] & registers[int(rt2, 2)]
        if category2[opcode2] == 'OR':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] | registers[int(rt2, 2)]
        if category2[opcode2] == 'XOR':
            registers[int(rd2, 2)] = registers[int(rs2, 2)] ^ registers[int(rt2, 2)]
        if category2[opcode2] == 'NOR':
            registers[int(rd2, 2)] = (registers[int(rs2, 2)] | registers[int(rt2, 2)]) ^ 2147483648

    if leftmost == '111':
        # 111 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | immediate_value(16 bits)
        # rt ← rs (ins) immediate
        rs3, rt3, opcode3, immediate = instr[3:8], instr[8:13], instr[13:16], instr[16:32]
        if category3[opcode3] == 'ADDI':
            registers[int(rt3, 2)] = registers[int(rs3, 2)] + int(immediate, 2)
        if category3[opcode3] == 'ANDI':
            registers[int(rt3, 2)] = registers[int(rs3, 2)] & int(immediate, 2)
        if category3[opcode3] == 'ORI':
            registers[int(rt3, 2)] = registers[int(rs3, 2)] | int(immediate, 2)
        if category3[opcode3] == 'XORI':
            registers[int(rt3, 2)] = registers[int(rs3, 2)] ^ int(immediate, 2)

    return registers, dataSegmDict


# 指令译码
def ins_decode(il, type):
    if il == '':
        return ''
    leftmost = il[0:3]
    if type == 1:
        ll = []  # 添加指令解析部分
    if type == 2:
        ll = ''

    # 第一类指令:
    if leftmost == '000':
        # 000 | opcode(3 bits) | Same as MIPS instruction
        opcode1, rs1, rt1, rd1 = il[3:6], il[6:11], il[11:16], il[16:21]
        # J | instr_index(26)
        jAddr = il[6:32]  # 跳转地址
        # BEQ | rs(5) | rt(5) | offset(16)     if rs = rt then branch
        # BGTZ | rs(5) | 00000 | offset(16)    if rs > 0 then branch
        # SW | base(5) | rt(5) | offset(16)     memory[base+offset] ← rt
        # LW | base(5) | rt(5) | offset(16)     rt ← memory[base+offset]
        offset = il[16:32]  # 跳转偏移量
        base = il[6:11]  # SW LW 的 base

        if type == 1:
            ll = il + '\t' + category1[opcode1]  # 添加指令类型  ins_decode
        if type == 2:
            ll = category1[opcode1]  # ins_decode2
        # print(ll)

        if category1[opcode1] == 'J':
            ll += ' #' + str(int(jAddr, 2) * 4)
        if category1[opcode1] == 'BEQ':
            ll += ' R' + str(int(rs1, 2)) + ', R' + str(int(rt1, 2)) + ', #' + str(int(offset, 2) * 4)
        if category1[opcode1] == 'BGTZ':
            ll += ' R' + str(int(rs1, 2)) + ', #' + str(int(offset, 2) * 4)
        if category1[opcode1] == 'SW' or category1[opcode1] == 'LW':
            ll += ' R' + str(int(rt1, 2)) + ', ' + str(int(offset, 2)) + '(R' + str(int(base, 2)) + ')'
            # print(ll)

    # 第二类指令:
    if leftmost == '110':
        # 110 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | rd(5 bits) | 00000000000
        # rd ← rs (ins) rt
        rs2, rt2, opcode2, rd2 = il[3:8], il[8:13], il[13:16], il[16:21]

        if type == 1:
            ll = il + '\t' + category2[opcode2] + ' R' + str(int(rd2, 2)) + ', R' + str(int(rs2, 2)) + ', R' + str(
                int(rt2, 2))
        if type == 2:
            ll = category2[opcode2] + ' R' + str(int(rd2, 2)) + ', R' + str(int(rs2, 2)) + ', R' + str(
                int(rt2, 2))  # ins_decode2
            # print(ll)

    # 第三类指令:
    if leftmost == '111':
        # 111 | rs(5 bits) | rt(5 bits) | opcode(3 bits) | immediate_value(16 bits)
        # rt ← rs (ins) immediate
        rs3, rt3, opcode3, immediate = il[3:8], il[8:13], il[13:16], il[16:32]

        if type == 1:
            ll = il + '\t' + category3[opcode3] + ' R' + str(int(rt3, 2)) + ', R' + str(int(rs3, 2)) + ', #' + str(
                int(immediate, 2))
        if type == 2:
            ll = category3[opcode3] + ' R' + str(int(rt3, 2)) + ', R' + str(int(rs3, 2)) + ', #' + str(
                int(immediate, 2))  # ins_decode2
            # print(ll)

    if type == 1:
        ll += '\n'
        return ll
    if type == 2:
        return '[' + ll + ']'


def data_decode(dl):
    if dl[0] == '0':  # 正数
        dl += '\t' + str(int(dl[0:32], 2))
    else:  # 负数
        dl += '\t-' + str((2147483647 ^ int(dl[1:32], 2)) + 1)
    dl += '\n'

    return dl


# 指令预处理
def ins_to_dict(instructions):
    insDict = {}
    # 字典:  {'instr地址':instruction, 地址: 32位指令}
    insDict[instructions[33:36]] = instructions[0:32]
    insDict['instr' + instructions[33:36]] = instructions[37:].strip()
    # print(insDict)     # {'128': '11000000000000000000100000000000', 'instr128': 'ADD R1, R0, R0'} ...
    return insDict


# 数据预处理
def data_to_dict(data):
    dataDict = {}
    # 字典:  {地址: 值}
    if data[0] == '0':
        dataDict[data[-3:]] = int(data[0:32], 2)
    else:
        dataDict[data[-3:]] = -((2147483647 ^ int(data[1:32], 2)) + 1)
    # print(dataDict)    # {'184': -1} , {'188': -2} ...
    return dataDict


def main(argv):
    inputfilename = ''
    try:
        opts, args = getopt.getopt(argv, "hi:", ["ifile="])  # 命令行参数
    except getopt.GetoptError:
        print('MIPSsim.py -i <inputfilename>')
        sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print('MIPSsim.py -i <inputfilename>')
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfilename = arg
    # print('输入的文件为：', inputfilename)
    simulator(proj_path + '/' + inputfilename)

# print(len(sys.argv))
# print(type(sys.argv))
# print(str(sys.argv))
# for a in range(0, len(sys.argv)):
#   print(sys.argv[a])

if __name__ == "__main__":
    main(sys.argv[1:])
