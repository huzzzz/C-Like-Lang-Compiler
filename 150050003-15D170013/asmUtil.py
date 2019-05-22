#!/usr/bin/python3
import os
import sys
import ply.lex as lex
import ply.yacc as yacc
from util import *
from node import Node, SymTableEntryVar, SymTableEntryProc
from globalVars import *
import heapq
import re
from heapq import heappop as pop, heappush as push

output_s = ""
scope_stack = []

tokens = (
	'NUMBER', 'FNUMBER',
	'PLUS', 'MINUS', 'MUL', 'DIVIDE', 'EQUALS', 
	'ID', 'GOTO', 'BB', 'COMMAS', 'FUNCTION', 'REF', 'DTYPE',
	'LPAREN', 'RPAREN', 'RETURN', 'NOT',
	'BOOLOPS', 'COMP',
	'IF', 'ELSE', 'NEWLINE'
)

data_types_list = [
	'int',
	'float',
]

t_ignore = " \t"

t_COMP = r'==|!=|<=|>=|<|>'
t_BOOLOPS = r'\|\||\&\&'
t_NOT = r'!'
t_EQUALS = r'='
t_REF = r'&'
t_COMMAS = r','
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_PLUS = r'\+'
t_MINUS = r'-'
t_MUL = r'\*'
t_DIVIDE = r'/'

heapq.heapify(heap_regs_d)
heapq.heapify(heap_regs_f)

functCallArgList = []

def t_NEWLINE(t):
	r'\n+'
	t.lexer.lineno += len(t.value)
	return t

def t_BB(t):
	"<bb"
	return t

def t_FNUMBER(t):
	r'\d+\.\d+'
	return t

def t_NUMBER(t):
	r'\d+'
	return t

def t_ID(t):
	r'[a-zA-Z_][a-zA-Z0-9_]*'
	
	if t.value in data_types_list:
		t.type = 'DTYPE'
	elif t.value == 'if':
		t.type = 'IF'
	elif t.value == 'else':
		t.type = 'ELSE'
	elif t.value == 'return':
		t.type = 'RETURN'
	elif t.value == 'goto':
		t.type = 'GOTO'
	elif t.value == 'function':
		t.type = 'FUNCTION'
	# elif t.value == 'bb':
	# 	t.type = 'BB'
	return t

def t_error(t): 
	print("Illegal character %s" % t.value[0])
	t.lexer.skip(1)

precedence = (
	('left', 'PLUS', 'MINUS'),
		('left', 'MUL', 'DIVIDE'),
		('right', 'UMINUS'),
		('right', 'IF', 'ELSE'),
		('right', 'STAR'),
)

def p_cfg(p):
	"""
		cfg : functiongrp
			| NEWLINE cfg
	"""
	if len(p) == 2:
		p[0] = p[1]
	else:
		p[0] = p[2]

	global output_s
	output_s = p[0]

def p_functiongrp(p):
	"""
		functiongrp : function functiongrp
					| function
	"""
	if len(p) == 3:
		p[0] = p[1] + p[2]
	else :
		p[0] = p[1]

def p_function(p):
	"""
		function : funchead NEWLINE funcbody
				| funchead NEWLINE
	"""
	if len(p) == 4:
		p[0] = p[1] + p[3]
	else:
		p[0] = p[1]

	global scope_stack
	scope_stack.pop()

def p_funchead(p):
	"""
		funchead : FUNCTION ID LPAREN formal_args RPAREN 
	"""
	p[0] =  getPrologueCallee(p[2])		# Call function callee prologue
	scope_stack.append(p[2])

def p_funcbody(p):
	"""
		funcbody : block funcbody
				| block
	"""
	if len(p) == 3:
		p[0] = p[1] + p[2]
	else:
		p[0] = p[1] + getEpilogueCallee(scope_stack[-1])

def p_block(p):
	"""
		block : bb NEWLINE blockbody
	"""
	p[0] = p[1] + ":\n" + p[3]

def p_blockbody(p):
	"""
		blockbody : statement blockbody 
				| 	statement_end
	"""
	if len(p) == 3:
		p[0] = p[1] + p[2]
	else:
		p[0] = p[1]	

def p_statement_end(p):
	"""
		statement_end : return NEWLINE
				| statement
	"""
	p[0] = p[1]

def p_statement(p):
	"""
		statement : assignment NEWLINE
				|	if_statement NEWLINE
				|	else_statement NEWLINE
				| 	GOTO bb NEWLINE
				| 	funct_call_only NEWLINE
	"""
	if len(p) == 3:
		p[0] = p[1]
	else:
		p[0] = "\tj " + p[2] + "\n"

def p_assignment_ID(p):
	"""
		assignment : ID EQUALS rval
	"""
	global temp_reg_map
	p[0] = p[3].split('@')[0]
	rval_reg = p[3].split('@')[1]

	store_str = "\tsw "
	if rval_reg[1] == 'f':
		store_str =  "\ts.s "
	if (p[1],scope_stack[-1]) in global_variable_table:
		offset = str(global_variable_table[(p[1],scope_stack[-1])].offset)
		p[0] += store_str + rval_reg+", "+str(offset)+"($sp)\n"
	elif (p[1], 'global') in global_variable_table:
		p[0] += store_str + rval_reg+", global_"+p[1]+"\n"		
	else:
		if rval_reg[1] == 'f':
			temp_reg_map[p[1]] = pop(heap_regs_f)
			p[0] += "\tmov.s " + temp_reg_map[p[1]] + ", " + rval_reg + "\n"
		else :
			temp_reg_map[p[1]] = pop(heap_regs_d)
			p[0] += "\tmove " + temp_reg_map[p[1]] + ", " + rval_reg + "\n"

	free_reg(rval_reg)

def p_assignment_pvar(p):
	"""
		assignment : pvar EQUALS rval
	"""

	p[0] = p[3].split('@')[0]
	
	rval_reg = p[3].split('@')[1]

	name_lval = extract_name_str(p[1])
	loi = get_loi_str(p[1])
	lval_reg_temp = pop(heap_regs_d)

	if (name_lval,scope_stack[-1]) in global_variable_table:
		offset = global_variable_table[(name_lval,scope_stack[-1])].offset
		p[0] += "\tlw " + lval_reg_temp + ", "+str(offset) +"($sp)\n"
	else:
		p[0] += "\tlw " + lval_reg_temp + ", global_"+ name_lval + "\n"

	for l in range(loi - 1):
		lval_reg_temp2 = pop(heap_regs_d)
		p[0] += "\tlw " + lval_reg_temp2 + ", 0("+lval_reg_temp+")\n"
		free_reg(lval_reg_temp)
		lval_reg_temp = lval_reg_temp2

	store_str = "\tsw "
	if rval_reg[1] == 'f':
		store_str = "\ts.s "

	p[0] += store_str+rval_reg+", 0("+lval_reg_temp+")\n"

	free_reg(rval_reg)
	free_reg(lval_reg_temp)

def p_pvar(p):
	"""
		pvar : MUL pvar %prec STAR
			| MUL ID %prec STAR
			| MUL pref %prec STAR
	"""
	p[0] = p[1] + p[2]

def p_ref(p):
	"""
		pref : REF ID
			| REF pvar
	"""
	p[0] = p[1] + p[2]

def p_rval(p):
	"""
		rval : expression PLUS expression
		    | expression MINUS expression
		    | expression DIVIDE expression
		    | expression MUL expression
		    | NOT expression
		    | expression
	"""	
	if len(p) == 2:
		p[0] = p[1]
	
	elif len(p) == 3:
		reg = p[2].split('@')[1]
		temp_reg = ""
		if reg[1] == 'f':
			tempreg = pop(heap_regs_f)
		else:
			tempreg = pop(heap_regs_d)
		p[0] = p[2].split('@')[0]
		p[0] += "\txori "+tempreg+", "+reg+", 1\n"
		free_reg(reg)
		p[0] += "@"+ tempreg
	else:
		# Cases for binary operations
		p[0] = p[1].split('@')[0] + p[3].split('@')[0]
		reg1 = p[1].split('@')[1]
		reg2 = p[3].split('@')[1]

		temp_reg = ""
		if reg1[1] == 'f' or reg2[1] == 'f':
			temp_reg = pop(heap_regs_f)
			if p[2] == '+':
				p[0] += "\tadd.s "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"
			elif p[2] == '-':
				p[0] += "\tsub.s "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
			elif p[2] == '*':
				p[0] += "\tmul.s "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
			elif p[2] == '/':
				p[0] += "\tdiv.s "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"
		else:
			temp_reg = pop(heap_regs_d)

			if p[2] == '+':
				p[0] += "\tadd "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"
			elif p[2] == '-':
				p[0] += "\tsub "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
			elif p[2] == '*':
				p[0] += "\tmul "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
			elif p[2] == '/':
				p[0] += "\tdiv "+ reg1 +", "+ reg2 +"\n"
				p[0] += "\tmflo " + temp_reg + "\n"	

		free_reg(reg1)
		free_reg(reg2)

		p[0] += "@" + temp_reg

def p_rval_comp(p):
	"""
		rval : expression COMP expression
	"""
	global float_cond_no
	p[0] = p[1].split('@')[0] + p[3].split('@')[0]
	reg1 = p[1].split('@')[1]
	reg2 = p[3].split('@')[1]

	float_cond_no_s = str(float_cond_no)
	
	temp_reg = ""
	if reg1[1] == 'f' or reg2[1] == 'f':
		temp_reg = pop(heap_regs_d)
		if p[2] == '==':
			p[0] += "\tc.eq.s "+ reg1 +", "+ reg2 +"\n"
		elif p[2] == '<=':
			p[0] += "\tc.le.s "+ reg1 +", "+ reg2 +"\n"		
		elif p[2] == '>=':
			p[0] += "\tc.le.s "+ reg2 +", "+ reg1 +"\n"		
		elif p[2] == '<':
			p[0] += "\tc.lt.s "+ reg1 +", "+ reg2 +"\n"				
		elif p[2] == '>':
			p[0] += "\tc.lt.s "+ reg2 +", "+ reg1 +"\n"	

		if p[2] == '!=':
			p[0] += "\tc.eq.s "+ reg1 +", "+ reg2 +"\n"		
			p[0] += "\tbc1f L_CondTrue_"+float_cond_no_s+"\n"
			p[0] += "\tli "+temp_reg+", 0\n"
			p[0] += "\tj L_CondEnd_"+float_cond_no_s+"\n"
			p[0] += "L_CondTrue_"+float_cond_no_s+":\n"
			p[0] += "\tli "+temp_reg+", 1\n"
			p[0] += "L_CondEnd_"+float_cond_no_s+":\n"
		else:
			p[0] += "\tbc1f L_CondFalse_"+float_cond_no_s+"\n"
			p[0] += "\tli "+temp_reg+", 1\n"
			p[0] += "\tj L_CondEnd_"+float_cond_no_s+"\n"
			p[0] += "L_CondFalse_"+float_cond_no_s+":\n"
			p[0] += "\tli "+temp_reg+", 0\n"
			p[0] += "L_CondEnd_"+float_cond_no_s+":\n"
		float_cond_no += 1
	else:
		temp_reg = pop(heap_regs_d)
		if p[2] == '==':
			p[0] += "\tseq "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"
		elif p[2] == '!=':
			p[0] += "\tsne "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
		elif p[2] == '<=':
			p[0] += "\tsle "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
		elif p[2] == '>=':
			p[0] += "\tsle "+ temp_reg +", "+ reg2 +", "+ reg1 +"\n"		
		elif p[2] == '<':
			p[0] += "\tslt "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"				
		elif p[2] == '>':
			p[0] += "\tslt "+ temp_reg +", "+ reg2 +", "+ reg1 +"\n"	

	free_reg(reg1)
	free_reg(reg2)

	p[0] += "@" + temp_reg			

def p_rval_boolops(p):
	"""
		rval : expression BOOLOPS expression
	"""
	p[0] = p[1].split('@')[0] + p[3].split('@')[0]
	reg1 = p[1].split('@')[1]
	reg2 = p[3].split('@')[1]

	temp_reg = ""
	if reg1[1] == 'f' or reg2[1] == 'f':
		temp_reg = pop(heap_regs_f)
	else:
		temp_reg = pop(heap_regs_d)

	if p[2] == '&&':
		p[0] += "\tand "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"
	else:
		p[0] += "\tor "+ temp_reg +", "+ reg1 +", "+ reg2 +"\n"		
	
	free_reg(reg1)
	free_reg(reg2)

	p[0] += "@" + temp_reg	

def p_expr_num(p):
	"""
		expression : NUMBER
	"""
	tempreg = pop(heap_regs_d)
	p[0] = "\tli " + tempreg + ", " + p[1] + "\n@" + tempreg

def p_expr_functcall(p):
	"""
		expression : funct_call
	"""
	p[0] = p[1]

def p_expr_fnum(p):
	"""
		expression : FNUMBER
	"""
	tempreg = pop(heap_regs_f)
	p[0] = "\tli.s " + tempreg + ", " + p[1] + "\n@" + tempreg

def p_expression_uminus(p):
	'expression : MINUS expression %prec UMINUS'
	expr_reg = p[2].split("@")[1]
	temp_reg = ""
	if expr_reg[1] == 'f':
		temp_reg = pop(heap_regs_f)
		p[0] = p[2].split("@")[0] + "\tneg.s " + temp_reg + ", " + expr_reg + "\n"
	else:
		temp_reg = pop(heap_regs_d)
		p[0] = p[2].split("@")[0] + "\tnegu " + temp_reg + ", " + expr_reg + "\n"
	p[0] += "@" + temp_reg

	free_reg(expr_reg)

def p_expr_pvar(p):
	"""
		expression : pvar
			| pref
			| ID
	"""
	p[0] = ""
	loi = get_loi_str(p[1])
	name = extract_name_str(p[1])
	
	if loi == -1:
		tempreg = pop(heap_regs_d)
		if (name, scope_stack[-1]) in global_variable_table:
			offset = str(global_variable_table[(name, scope_stack[-1])].offset)
			p[0] += "\taddi "+ tempreg +", $sp, " + offset + "\n"
		else:
			p[0] += "\tla "+ tempreg +", global_" + name + "\n"

		p[0] += "@" + tempreg

	elif loi == 0:
		if isFloatReg((name, scope_stack[-1])):
			tempreg = pop(heap_regs_f)
			start_str = "\tl.s" + tempreg
		else:
			tempreg = pop(heap_regs_d)
			start_str = "\tlw "+ tempreg 

		if (name, scope_stack[-1]) in global_variable_table:
			offset = str(global_variable_table[(name, scope_stack[-1])].offset)
			p[0] += start_str +", "+ offset +"($sp)\n"
		elif (name, 'global') in global_variable_table:
			p[0] += start_str +", global_" + name + "\n"
		else:
			free_reg(tempreg)
			tempreg = temp_reg_map[name]
		p[0] += "@" + tempreg
		
	else:
		tempreg = pop(heap_regs_d)

		derivedType = ""
		base_type = ""

		if (name, scope_stack[-1]) in global_variable_table:
			offset = str(global_variable_table[(name, scope_stack[-1])].offset)
			derivedType = global_variable_table[(name, scope_stack[-1])].loi
			base_type = global_variable_table[(name, scope_stack[-1])].base_type
			p[0] = "\tlw "+ tempreg +", "+ offset +"($sp)\n"
		else:
			base_type = global_variable_table[(name, 'global')].base_type
			derivedType = global_variable_table[(name, 'global')].loi
			p[0] += "\tlw "+ tempreg +", global_" + name + "\n"	
		
		for l in range(loi - 1):
			tempreg2 = pop(heap_regs_d)
			p[0] += "\tlw " + tempreg2 + ", 0("+tempreg+")\n"
			free_reg(tempreg)
			tempreg = tempreg2
		
		if loi == derivedType and base_type == 'float':
			tempreg2 = pop(heap_regs_f)
			p[0] += "\tl.s " + tempreg2 + ", 0("+tempreg+")\n"
			free_reg(tempreg)
			tempreg = tempreg2
			
		else:
			tempreg2 = pop(heap_regs_d)
			p[0] += "\tlw " + tempreg2 + ", 0("+tempreg+")\n"
			free_reg(tempreg)
			tempreg = tempreg2

		p[0] += "@" + tempreg

def p_if_statement(p):
	"""
		if_statement : IF LPAREN ID RPAREN GOTO bb
	"""
	p[0] = "\tbne "+ temp_reg_map[p[3]] +", $0, " + p[6] + "\n"
	free_reg(temp_reg_map[p[3]])

def p_else_statement(p):
	"""
		else_statement : ELSE GOTO bb
	"""
	p[0] = "\tj " + p[3] + "\n"

def p_bb(p):
	"""
		bb : BB NUMBER COMP 
	"""
	p[0] = "label" + p[2]

def p_return(p):
	"""
		return : RETURN expression
				| RETURN
	"""
	p[0] = ""
	if len(p) == 3:
		reg = p[2].split('@')[1]
		p[0] += p[2].split('@')[0]
		if reg[1] == 'f':
			p[0] += "\tmov.s $f0, "+reg+" # move return value to $f0\n"
		else:
			p[0] += "\tmove $v1, "+ reg +" # move return value to $v1\n"
		free_reg(reg)

	p[0] += "\tj epilogue_"+scope_stack[-1] +"\n\n"

def p_function_call(p):
	"""
		funct_call : FUNCNAME_DUMMY LPAREN args RPAREN
	"""

	argList = global_procedure_table[p[1]].paramList
	
	len_sp = 0

	for arg in argList:
		if arg[1][1] == 0 and arg[1][0] == 'float':
			len_sp += 8
		else:
			len_sp += 4	

	p[0] = "\t# setting up activation record for called function\n"
	p[0] += p[3]
	p[0] += "\tsub $sp, $sp, " + str(len_sp) + "\n"
	p[0] += "\tjal " + p[1] + " # function call\n"
	p[0] += "\tadd $sp, $sp, " + str(len_sp) + " # destroying activation record of called function\n"
	if global_procedure_table[p[1]].returnType == ('float', 0):
		tempreg = pop(heap_regs_f)
		p[0] += "\tmov.s "+tempreg+", $f0 # using the return value of called function\n"
	else:	
		tempreg = pop(heap_regs_d)
		p[0] += "\tmove "+tempreg+", $v1 # using the return value of called function\n"
	p[0] += "@" + tempreg

def p_function_call_only(p):
	"""
		funct_call_only : FUNCNAME_DUMMY LPAREN args RPAREN
	"""

	argList = global_procedure_table[p[1]].paramList
	
	len_sp = 0

	for arg in argList:
		if arg[1][1] == 0 and arg[1][0] == 'float':
			len_sp += 8
		else:
			len_sp += 4	

	p[0] = "\t# setting up activation record for called function\n"
	p[0] += p[3]
	p[0] += "\tsub $sp, $sp, " + str(len_sp) + "\n"
	p[0] += "\tjal " + p[1] + " # function call\n"
	p[0] += "\tadd $sp, $sp, " + str(len_sp) + " # destroying activation record of called function\n"

def p_FUNCNAME_DUMMY(p):
	"""
		FUNCNAME_DUMMY : ID  
	"""

	global functCallArgList
	functCallArgList = [list(global_procedure_table[p[1]].paramList), 0]
	p[0] = p[1]

def p_args(p):
	"""
		args : varlist
			|	
	"""
	if len(p) == 1:
		p[0] = ""
	else:
		p[0] = p[1]

def p_varlist(p):
	"""
		varlist : vararg COMMAS varlist
				| vararg
	"""
	
	currArg = functCallArgList[0].pop()

	reg_temp = p[1].split('@')[1]
	
	p[0] = p[1].split('@')[0]
	
	if currArg[1] == ("float", 0):
		p[0] += "\ts.s "+reg_temp+", "+str(functCallArgList[1])+"($sp)\n"
		functCallArgList[1] -= 8
	else:
		p[0] += "\tsw "+reg_temp+", "+str(functCallArgList[1])+"($sp)\n"
		functCallArgList[1] -= 4

	if len(p) == 4:
		p[0] += p[3]

def p_vararg(p):
	"""
		vararg : expression
	"""
	
	reg_temp = p[1].split('@')[1]
	
	p[0] = p[1]
	
	free_reg(reg_temp)

def p_formal_args(p):
	"""
		formal_args : formal_arg COMMAS formal_args
			|	formal_arg
			|
	"""
	
def p_formal_arg(p):
	"""
		formal_arg : DTYPE ID
					| DTYPE pvar
					| DTYPE pref 
	"""

def p_error(p):
	if p:
		errStr = "CFG syntax error at '{0}' line no '%d'".format(p.value) % p.lexer.lineno
	else:
		errStr = "CFG syntax error at EOF"
	print(errStr)
	
def traverseNodeAsm(Node, file_name):
	modifySymTableOffsets()
	lines = ""
	with open(file_name, 'r') as f: 
		lines = f.readlines()

	data = ''.join(lines)
	output = "\n"
	output += printData()

	process(data)
	output += output_s
	return output

def modifySymTableOffsets():
	global global_variable_table 
	global global_procedure_table

	keyes = list(global_variable_table.keys())
	scopes = [key[1] for key in keyes]	
	scopes = list(set(scopes))
	for scope in scopes:

		curr_keys = []
		for key in keyes:
			if key[1] == scope:
				curr_keys.append(key)
		curr_keys.sort()
		offset = 0
		for key in curr_keys:
			if global_variable_table[key].isParam == False:
				offset += global_variable_table[key].width
				global_variable_table[key].offset = offset
	
	keyes_proc = list(global_procedure_table.keys())

	for scope in keyes_proc:
		offset = global_procedure_table[scope].width + 8
		paramList = global_procedure_table[scope].paramList
		paramList = []
		for key in global_variable_table:
			if key[1] == scope and global_variable_table[key].isParam == True:
				paramList.append((key, global_variable_table[key]))
		paramList.sort(key = lambda x : x[1].offset)
		for param in paramList:
			offset += global_variable_table[param[0]].width
			global_variable_table[param[0]].offset = offset 

def process(data):
	lex.lex()
	yacc.yacc()
	yacc.parse(data)

def printData():
	output = "\t.data\n"
	keyes = list(global_variable_table.keys())
	keyes.sort()
	for key in keyes:
		if key[1] == 'global':
			dataval = global_variable_table[key]
			curr_size = dataval.width
			if curr_size == 4 :
				output += 'global_' + key[0] + ":\t.word\t0\n"
			elif curr_size == 8:
				output += 'global_' + key[0] + ":\t.space\t8\n"

	output += "\n"	
	return output

def printAsmUtil(Node):
	output = ""
	output += "\t.text\t# The .text assembler directive indicates\n"
	output += "\t.globl " + extractName(Node.leaf) + "\t# The following is the code\n"
	output += extractName(Node.leaf) + ":\n"
	#Function Prologue
	output += getPrologueCallee(extractName(Node.leaf))
	output += getAsmBody(Node.children[2], extractName(Node.leaf))
	output += getEpilogueCallee(extractName(Node.leaf))

	return output

def getAsmBody(Node, name):
	output = ""
	if len(Node.children) == 0:
		return output
	else:
		if Node.children[0].type == 'DECLARATIONS':
			return getAsmBody(Node.children[1], name)
		output += "label" + Node.leaf + ":\n"
		if Node.children[0].type == 'RETURN':
			if len(Node.children[0].children) != 0:
				output += getAsmExpr(Node.children[0].children[0], name)
			output += "\tj epilogue_" + name + "\n"

	output += getAsmBody(Node.children[1], name)
	return output

def getAsmExpr(Node, name):
	output = ""
	if Node.type == "CONST":
		if re.match('[0-9]+.[0-9]+', Node.leaf) is not None:
			reg_used = heapq.heappop(heap_regs_f)
		else :
			reg_used = heapq.heappop(heap_regs_d)
		output += "\tli " + reg_used + " "  + Node.leaf + "\n"
		Node.leaf = reg_used
	# elif Node.type == "VAR":


	return output

def getPrologueCallee(name):
	output = ""
	output += "\t.text	# The .text assembler directive indicates\n"
	output += "\t.globl " +name+"	# The following is the code\n"
	output += name+":\n"
	output += "# Prologue begins\n"
	output += "\tsw $ra, 0($sp)	# Save the return address\n"
	output += "\tsw $fp, -4($sp)	# Save the frame pointer\n"
	output += "\tsub $fp, $sp, 8	# Update the frame pointer\n"
	output += "\tsub $sp, $sp, " + str(global_procedure_table[name].width + 8) + "	# Make space for the locals\n"
	output += "# Prologue ends\n"

	return output

def getEpilogueCallee(name):

	output = "# Epilogue begins\n"
	output += "epilogue_"+ name+":\n"
	output += "\tadd $sp, $sp, " + str(global_procedure_table[name].width + 8) + "\n"
	output += "\tlw $fp, -4($sp)\n"
	output += "\tlw $ra, 0($sp)\n"
	output += "\tjr $ra	# Jump back to the called procedure\n"
	output += "# Epilogue ends\n"

	return output
	
def isFloatReg(name):
	if name in global_variable_table:
		return global_variable_table[name].base_type == 'float' and global_variable_table[name].loi == 0
	else:
		if (name[0], 'global') in global_variable_table:
			return global_variable_table[(name[0], 'global')].base_type == 'float' and global_variable_table[(name[0], 'global')].loi == 0
		else:
			return temp_reg_map[name[0]][1] == 'f'