#!/usr/bin/python3

import os
import sys
import ply.lex as lex
import ply.yacc as yacc
import collections 
from itertools import chain
from astUtil import traverseNode
from cfgUtil import traverseNodeCfg
from asmUtil import traverseNodeAsm
from util import *
from node import Node, SymTableEntryVar, SymTableEntryProc
from globalVars import *

tokens = (
		'NUMBER', 'FNUMBER',
		'PLUS', 'MINUS', 'DIVIDE', 'EQUALS', 'STAR',
		'LPAREN', 'RPAREN',
		'ID', 'KEYWORD', 'COMMAS' , 'REF', 'DELIM', 'DTYPE',
		'SEMIC', 'BOOLOPS', 'COMP', 'NOT',
		'IF', 'ELSE', 'WHILE',
)

keyword_list = [
	'main',
	'return',
]

data_types_list = [
	'int',
	'float',
	'void',
]

delimiters_list = ['{', '}']

 
# Define a rule so we can track line numbers
def t_newline(t):
	r'\n+'
	t.lexer.lineno += len(t.value)
	# print(t.lexer.lineno)

t_ignore = " \t"
t_ignore_COMMENTS = r'//.*'

t_COMP = r'==|!=|<=|>=|<|>'
t_BOOLOPS = r'\|\||\&\&'
t_NOT = r'!'
t_EQUALS = r'='
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_DELIM = r'{|}'
t_REF = r'&'
t_COMMAS = r','
t_SEMIC = r';'
t_PLUS = r'\+'
t_MINUS = r'-'
t_STAR = r'\*'
t_DIVIDE = r'/'

output_to_txtfile = ""
output_to_txtfile_cfg = ""
output_to_txtfile_asm = ""

p0 = ""
tempvarscnt = 0

temp_dict = collections.OrderedDict()

scope_stack = ['global']
offset_stack = [0] 

curr_var = ''

def findVarNameEntry(nameArg):
	temp = scope_stack.copy()
	while len(temp) != 0 :
		if (nameArg, temp[-1]) in global_variable_table :
			tempNode = global_variable_table[(nameArg, temp[-1])]
			return (tempNode.base_type, tempNode.loi)
		else :
			temp.pop()
	return ""

def t_FNUMBER(t):
	r'\d+\.\d+'
	return t

def t_NUMBER(t):
	r'\d+'
	return t

def t_ID(t):
	r'[a-zA-Z_][a-zA-Z0-9_]*'
	
	if t.value in keyword_list:
		t.type = 'KEYWORD'
	elif t.value in data_types_list:
		t.type = 'DTYPE'
	elif t.value == 'if':
		t.type = 'IF'
	elif t.value == 'else':
		t.type = 'ELSE'
	elif t.value == 'while':
		t.type = 'WHILE'
	return t

def t_error(t): 
	print("Illegal character %s" % t.value[0])
	t.lexer.skip(1)

precedence = (
	('left', 'BOOLOPS'),
	('left', 'COMP'),
	('left', 'PLUS', 'MINUS'),
		('left', 'STAR', 'DIVIDE'),
		('right', 'UMINUS'),
		('right', 'IF', 'ELSE'),
)

def check_correctness(Node):
	children = Node.children
	if Node.type == "FUNCTCALL":
		return False
	if len(children) == 0:
		if Node.type == "CONST":
			return True
		else:
			return False
	else:
		res = True
		for child in children:
			res = res and check_correctness(child)
		return res

def printSymTable():
	global global_variable_table
	output = "Procedure table :-\n-----------------------------------------------------------------\n"
	output += "Name\t\t|\tReturn Type\t|\tParameter List\n"
	for proc, procval in global_procedure_table.items() :
		# print(procval[1])
		if proc != 'main':
			output += proc + "\t\t|\t" + getStrForm3(procval.returnType) + "\t\t|\t" + getStrNormFormArgs(procval.paramList) + "\n" 
	
	output += "-----------------------------------------------------------------\n"
	output += "Variable table :-\n"
	output += "-----------------------------------------------------------------\n"
	output += "Name\t|\tScope\t\t|\tBase Type\t|\tDerived Type\n"
	output += "-----------------------------------------------------------------\n"
	for var in global_variable_table :
		varval = global_variable_table[var]
		if var[1] == "global" :
			output += var[0] + "\t\t|\t" + var[1] + "\t\t|\t" + varval.base_type + "\t\t|\t" + varval.loi * "*" + "\n"
		else:
			output += var[0] + "\t\t|\t" + "procedure " + var[1] +  "\t|\t" + varval.base_type + "\t\t\t|\t" + varval.loi * "*" + "\n"
	output += "-----------------------------------------------------------------\n"
	output += "-----------------------------------------------------------------\n"
	return output

def p_prog(p):
	"""
		prog : subprog
	"""
	p[0] = p[1]
	global output_to_txtfile
	output_to_txtfile =  traverseNode(p[0])
	global output_to_txtfile_cfg
	modify(p[0])
	output_to_txtfile_cfg = traverseNodeCfg(p[0])
	p0 = p[0]

def p_subprog(p):
	"""
	subprog : declarations subprog 
		| funct_def subprog
		| main_funct subprog
		| funct_decl subprog
		|
	"""
	if len(p) == 1:
		p[0] = Node("PROG", [], "")
	else:
		p[0] = Node("PROG", [p[1]] + p[2].children, "")
	
def p_funcHead(p):
	"""
		funcHead : DTYPE var DUMMY LPAREN formal_args RPAREN
				|	DTYPE pvar DUMMY LPAREN formal_args RPAREN 	
	"""
	
	returnType = extractDerivedType(p[2])
	p[0] = Node("FUNCHEAD", [p[5], (p[1], returnType)], p[2])
	funcName = extractName(p[2])
	
	global global_procedure_table
	global global_defined_yet

	if funcName in global_defined_yet:
		if global_defined_yet[funcName] == 1:
			errStr = "Multiple definitions of function {0}() on line '%d'".format(funcName) % p.lexer.lineno
			printerr(errStr)	
		else:
			if not(global_procedure_table[funcName].returnType == (p[1], returnType)
			and all([x[1] == y[1] for x,y in zip(global_procedure_table[funcName].paramList, getList(p[5]))])) :
				errStr = "Different data types in declaration and definition of the function {0}() on line '%d'".format(funcName) % p.lexer.lineno
				printerr(errStr)

	if funcName not in global_defined_yet :
		global_procedure_table[funcName] = SymTableEntryProc((p[1], returnType), getList(p[5]), 0)
	global_defined_yet[funcName] = 1

def p_function_def(p):
	"""
		funct_def : funcHead DELIM DUMMY0 body DELIM
	"""
	if not (p[2] == '{' and p[5] == '}'):
		print("syntax error at '{0}' line no '%d'".format(p[1]) % p.lexer.lineno)
		print_to_output_file_cfg("")
		print_to_output_file()
		sys.exit()

	p[0] = Node("FUNCTION", p[1].children + [p[4]], p[1].leaf)
	global scope_stack
	global offset_stack
	global global_procedure_table
	global_procedure_table[scope_stack[-1]].width = offset_stack[-1]
	scope_stack.pop()
	offset_stack.pop()

def p_mainfunct(p):
	'main_funct : DTYPE KEYWORD DUMMY2 LPAREN RPAREN DELIM body DELIM'

	if not (p[1] == 'void' and p[2] == 'main' and p[6] == '{' and p[8] == '}'):
		errStr = "syntax error at '{0}' line no '%d'".format(p[1]) % p.lexer.lineno
		printerr(errStr)

	p[0] = Node("FUNCTION", [Node("ARGS", [], ""),(p[1], 0), p[7]], Node("VAR", [], "main"))

	global scope_stack
	global offset_stack
	global global_procedure_table

	global_procedure_table[p[2]] = SymTableEntryProc((p[1], 0), [], offset_stack[-1])
	
	scope_stack.pop()
	offset_stack.pop()

def p_function_decl(p):
	"""
		funct_decl : DTYPE var DUMMY LPAREN formal_args RPAREN SEMIC
			| 	DTYPE pvar DUMMY LPAREN formal_args RPAREN SEMIC
	"""
	p[0] = Node("FUNCTDEC", [p[5]], p[2])
	returnType = extractDerivedType(p[2])
	funcName = extractName(p[2])

	global global_defined_yet
	global global_procedure_table
	global temp_dict

	temp_dict = collections.OrderedDict()

	if funcName not in global_procedure_table:
		global_procedure_table[funcName] = SymTableEntryProc((p[1], returnType), getList(p[5]), 0)
	else:
		errStr = "Multiple declaration of function {0}() on line '%d'".format(p[1]) % p.lexer.lineno
		printerr(errStr)

	global_defined_yet[funcName] = 0

	global scope_stack
	global offset_stack
	global_procedure_table[scope_stack[-1]].width = offset_stack[-1]
	scope_stack.pop()
	offset_stack.pop()

def p_function_call(p):
	"""
		funct_call : ID LPAREN args RPAREN
	"""
	expectedArgTypes = global_procedure_table[p[1]].paramList
	if len(p[3].children) == len(expectedArgTypes) :
		for i, arg in enumerate(p[3].children):
			if expectedArgTypes[i][1] != arg.node_type:
				errStr = "Different type in the parameters of call and declaration of the function {0}() on line '%d'".format(p[1]) % p.lexer.lineno
				printerr(errStr)
	else :
		errStr = "Different number of parameters of call and declaration of the function {0}() on line '%d'".format(p[1]) % p.lexer.lineno
		printerr(errStr)
		
	expr = p[1] + "(" + getStrArg(p[3]) + ")"
	p[0] = Node("FUNCTCALL", [p[3]], expr) 

def p_dummy(p):
	'DUMMY : '
	global scope_stack
	global offset_stack
	global decl_check
	decl_check = []
	scope_stack.append(curr_var)
	offset_stack.append(0)

def p_dummy0(p):
	'DUMMY0 : '
	global temp_dict
	global global_variable_table

	global_variable_table.update(temp_dict)
	temp_dict = collections.OrderedDict()

def p_dummy2(p):
	'DUMMY2 : '
	global scope_stack
	global offset_stack
	scope_stack.append('main')
	offset_stack.append(0)

def p_formal_args(p):
	"""
		formal_args : formal_arg COMMAS formal_args
			|	formal_arg
			|
	"""
	if len(p) == 2 :
		p[0] = Node("PARAMS", [p[1]], "")
	elif len(p) == 1 :
		p[0] = Node("PARAMS", [], "")
	else :
		p[0] = Node("PARAMS", [p[1]] + p[3].children, "")

def p_formal_arg(p):
	"""
		formal_arg : DTYPE genVar
	"""

	varName = extractName(p[2])
	derivedType = extractDerivedType(p[2])
	
	p[0] = Node("FORMALARG", [varName, p[1], derivedType], "")

	global temp_dict

	derivedType2 = get_loi(p[2])
	curr_width = 4
	if derivedType2 == 0 and p[1] == 'float':
		curr_width = 8

	temp_dict[(varName, scope_stack[-1])] = SymTableEntryVar(p[1], derivedType, len(temp_dict.keys()), curr_width, True)	

def p_args(p):
	"""
		args : exprlist
			|	
	"""
	if len(p) == 1:
		p[0] = Node("ARGS", [], "")
	else :
		p[0] = p[1]

def p_exprlist(p):
	"""
		exprlist : expression COMMAS exprlist
				| expression
	"""
	if len(p) == 2:
		p[0] = Node("ARGS", [p[1]], "")
	else :
		p[0] = Node("ARGS", [p[1]] + p[3].children, "")

def p_genVar(p):
	"""
		genVar : var
			| pvar
			| pref
	"""
	p[0] = p[1]

def p_body(p):
	"""
		body : subbody
	"""
	p[0] = p[1]

def p_subbody(p):
	"""
		subbody : declarations subbody
				| block subbody
				|
	"""
	if len(p) == 1:
		p[0] =  Node("SUBBODY", [], "")
	else:
		p[0] = Node("SUBBODY", [p[1], p[2]], "")

def p_block(p):
	"""
		block : single_assign SEMIC
				| if_else_statement
				| while_statement
				| funct_call SEMIC
				| return_statement
	"""
	p[0] = p[1]

def p_statement(p):
	"""
		statement : SEMIC
				| single_assign SEMIC
				| if_else_statement
				| while_statement
				| DELIM subbody DELIM
				| funct_call SEMIC
				| return_statement
	"""
	if len(p) == 2:
		if p[1] ==";":
			p[0] = Node("SUBBODY", [], "")
		else:
			p[0] = Node("SUBBODY", [p[1], Node("SUBBODY", [], "")], "")
	elif len(p) == 3:
		p[0] = Node("SUBBODY", [p[1], Node("SUBBODY", [], "")], "")
	else:
		if not (p[1] == '{' and p[3] == '}'):
			errStr = "syntax error at '{0}' line no '%d'".format(p[1]) % p.lexer.lineno
			printerr(errStr)
		else:
			p[0] = p[2]

def p_return(p):
	"""
		return_statement : KEYWORD expression SEMIC
					|	KEYWORD SEMIC
	"""
	if p[1] != 'return':
		errStr = "syntax error at '{0}' line no '%d'".format(p[1]) % p.lexer.lineno
		printerr(errStr)

	# print(global_procedure_table)
	if scope_stack[-1] == "main" :
		errStr = "syntax error at '{0}' line no '%d'".format(p[1]) % p.lexer.lineno
		printerr(errStr)
	expec_ret_type = global_procedure_table[scope_stack[-1]].returnType
	
	if len(p) == 3:
		if (expec_ret_type != ('void', 0)):
			errStr = "Type mismatch at {0} on line no %d".format(p[1]) % p.lexer.lineno
			printerr(errStr)
		p[0] = Node("RETURN", [], p[1])

	else:
		act_ret_type = p[2].node_type
		if (act_ret_type != act_ret_type):
			errStr = "Type mismatch at {0} on line no %d".format(p[1] + p[2].leaf) % p.lexer.lineno
			printerr(errStr)

		p[0] = Node("RETURN", [p[2]], p[1])

def p_if(p):
	"""
		if_statement : IF LPAREN cond RPAREN statement
	"""
	p[0] = Node("IF", [p[3], p[5]], p[1])

def p_else(p):
	"""
		else_statement : ELSE statement
	"""
	p[0] = p[2]

def p_if_else_statement(p):
	"""
		if_else_statement : if_statement %prec ELSE
						| 	if_statement else_statement  
	"""
	if len(p) == 2:
		p[0] = Node(p[1].type, p[1].children + [Node("SUBBODY", [], "")], p[1].leaf)
	else:
		p[0] = Node(p[1].type, p[1].children + [p[2]], p[1].leaf)

def p_while(p):
	"""
		while_statement : WHILE LPAREN cond RPAREN statement
	"""
	p[0] = Node("WHILE", [p[3], p[5]], p[1])

def p_condition(p):
	"""
		cond : cond BOOLOPS single_cond
			| single_cond
			| NOT LPAREN single_cond RPAREN
			| LPAREN single_cond RPAREN
			| cond BOOLOPS LPAREN single_cond RPAREN
	"""	
	global tempvarscnt
	if len(p) == 4:
		if p[1] == '(':
			p[0] = p[2]
		else:
			t = "t"+str(tempvarscnt)
			tempvarscnt += 1
			temp = " " + p[2] + " " 
			if p[2] == "&&":
				p[0] = Node("AND", [p[1], p[3]], t , t + " = " + p[1].leaf+temp+p[3].leaf)
			elif p[2] == "||":
				p[0] = Node("OR", [p[1], p[3]], t , t + " = " + p[1].leaf+temp+p[3].leaf)
	elif len(p) == 6:
		t = "t"+str(tempvarscnt)
		tempvarscnt += 1
		temp = " " + p[2] + " " 
		if p[2] == "&&":
			p[0] = Node("AND", [p[1], p[4]], t , t + " = " + p[1].leaf+temp+p[4].leaf)
		elif p[2] == "||":
			p[0] = Node("OR", [p[1], p[4]], t , t + " = " + p[1].leaf+temp+p[4].leaf)
	elif len(p) == 5:
		t = "t"+str(tempvarscnt)
		tempvarscnt += 1
		p[0] = Node("NOT", [p[3]], t, t + " = !" + p[3].leaf)
	else:
		p[0] = p[1]

def p_generic_expression(p):
	"""
		gen_expression : expression
					| NOT expression
	"""
	if len(p) == 2:
		p[0] = p[1]
	else:
		p[0] = Node("NOT", [p[2]], p[1] + p[2].leaf, node_type = p[2].node_type)

def p_single_condition(p):
	"""
		single_cond : gen_expression COMP gen_expression
	"""
	global tempvarscnt
	t = "t"+str(tempvarscnt)
	tempvarscnt += 1
	
	temp = " " + p[2] + " " 
	if len(p) == 4:
		if p[2] == "==":
			p[0] = Node("EQ", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)
		elif p[2] == "!=":
			p[0] = Node("NE", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)
		elif p[2] == "<=":
			p[0] = Node("LE", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)
		elif p[2] == ">=":
			p[0] = Node("GE", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)
		elif p[2] == ">":
			p[0] = Node("GT", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)
		elif p[2] == "<":
			p[0] = Node("LT", [p[1], p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf)

	l_type = p[1].node_type
	r_type = p[3].node_type

	if (l_type != r_type):
		errStr = "Type mismatch at {0} on line no %d".format(p[0].leaf) % p.lexer.lineno
		printerr(errStr)

def p_single_assign(p):
	"""
		single_assign : pvar EQUALS expression
					| var EQUALS expression 
	"""

	temp = " " + p[2] + " " 
	
	p[0] = Node("ASGN", [p[1],p[3]], p[1].leaf+temp+p[3].leaf)
	
	temp = findVarNameEntry(extractName(p[1]))

	if temp == "":
		errStr = "Use of undefined variable %s" % extractName(p[1])
		printerr(errStr)

	l_type = (temp[0], temp[1] + get_loi(p[1]))
	r_type = p[3].node_type

	if (l_type != r_type):
		errStr = "Type mismatch at {0} on line no %d".format(p[0].leaf) % p.lexer.lineno
		printerr(errStr)

	if p[1].type == "VAR":
		if check_correctness(p[3]) == True: 
			errStr = "Syntax error at {0} ".format(p[1].leaf +" "+ p[2])
			printerr(errStr)

def p_pvar(p):
	"""
		pvar : STAR pvar
			| STAR var
			| STAR pref
	"""
	p[0] = Node("DEREF", [p[2]], p[1]+p[2].leaf)

def p_ref(p):
	"""
		pref : REF var
			| REF pvar
	"""
	p[0] = Node("ADDR", [p[2]], p[1] + p[2].leaf)

def p_var(p):
	'var : ID'
	global curr_var
	curr_var = p[1]
	p[0] = Node("VAR", [], p[1])

def p_expression_var(p):
	"""
		expression : var
	"""
	p[0] = p[1]
	temp = findVarNameEntry(extractName(p[1]))
	if get_loi(p[0]) == 0 and temp[1] == 0:
		errStr = "direct use of non pointer variable {0} on line no %d".format(p[0].leaf) % p.lexer.lineno
		printerr(errStr)
	if (temp == ""):
		errStr = "Use of undefined variable %s" % extractName(p[1])
		printerr(errStr)
	p[0].node_type = (temp[0], temp[1] + get_loi(p[1])) 

def p_expression_pvar(p):
	"""
		expression : pvar
	"""
	p[0] = p[1]
	temp = findVarNameEntry(extractName(p[1]))
	if (temp == ""):
		errStr = "Use of undefined variable %s" % extractName(p[1])
		printerr(errStr)

	if temp[1] + get_loi(p[1]) < 0 :
		errStr = "Too much indirection on {0} on line no %d".format(p[0].leaf) % p.lexer.lineno
		printerr(errStr)
	p[0].node_type = (temp[0], temp[1] + get_loi(p[1])) 

def p_expression_deref(p):
	"""
		expression : pref
	"""
	p[0] = p[1]
	temp = findVarNameEntry(extractName(p[1]))
	if (temp == ""):
		errStr = "Use of undefined variable %s" % extractName(p[1])
		printerr(errStr)
	p[0].node_type = (temp[0], temp[1] + get_loi(p[1])) 
		
def p_expression_functcall(p):
	"""
		expression : funct_call
	"""
	p[0] = p[1]
	funcName = p[1].leaf.split("(")[0]
	p[0].node_type = global_procedure_table[funcName].returnType

def p_declarations(p):
	"""
		declarations : DTYPE list_ids SEMIC
	"""
	# print("I DECLARE AM GROOT")
	if p[1] != 'int' and p[1] != 'float':
		errStr = "declaration syntax error at '%s' line no '%d'" % (p[1], p.lexer.lineno)
		printerr(errStr)		
	p[0] = Node("DECLARATIONS", [p[2]], p[1])

	global global_variable_table
	global scope_stack
	global offset_stack

	for child in p[2].children:
		varName = extractName(child)
		varDerivedType = extractDerivedType(child)
		if ((varName, scope_stack[-1]) in global_variable_table):
			errStr = "Multiple declaration of variable %s" % varName
			printerr(errStr)
		else : 
			curr_width = 4
			
			if varDerivedType == 0: # Handling case when type is float
				curr_width = width_table[p[1]]
			
			global_variable_table[(varName, scope_stack[-1])] = SymTableEntryVar(p[1], varDerivedType, offset_stack[-1], curr_width, False)				
			offset_stack[-1] += curr_width

def p_list_ids(p):
	"""
		list_ids : var
				| var COMMAS list_ids
				| pvar
				| pvar COMMAS list_ids
	"""

	if len(p) == 2:
		p[0] = Node("LISTIDS", [p[1]], "")
	else:
		p[0] =  Node("LISTIDS", [p[1]] + p[3].children, p[2])	

def p_expression_binop(p):
		"""
		expression : expression PLUS expression
				  | expression MINUS expression
				  | expression STAR expression
				  | expression DIVIDE expression
		"""
		temp = " " + p[2] + " " 
		curr_op = ""
		if p[2] == '+':
			curr_op = "PLUS"
		elif p[2] == '-':
			curr_op = "MINUS"
		elif p[2] == '*':
			curr_op = "MUL"
		elif p[2] == '/':
			curr_op = "DIV"

		global tempvarscnt
		t = "t"+str(tempvarscnt)
		tempvarscnt += 1
		
		if (p[1].node_type == p[3].node_type):
			p[0] = Node(curr_op, [p[1],p[3]], t, t + " = " + p[1].leaf+temp+p[3].leaf, node_type=p[1].node_type)
		else:
			errStr = "type mis match at {0} on line no %d".format(p[1].leaf+temp+p[3].leaf) % p.lexer.lineno
			printerr(errStr)

		if p[1].node_type[1] != 0:
			errStr = "Pointer Arithmatic is not allowed {0} on line no %d".format(p[1].leaf+temp+p[3].leaf) % p.lexer.lineno
			printerr(errStr)


def p_expression_uminus(p):
		'expression : MINUS expression %prec UMINUS'
		# p[0] = '-' + p[2]
		global tempvarscnt
		t = "t"+str(tempvarscnt)
		tempvarscnt += 1
		
		p[0] = Node("UMINUS", [p[2]], t, t + " = " + p[1]+p[2].leaf, node_type=p[2].node_type)

def p_expression_group(p):
		'expression : LPAREN expression RPAREN'
		rep[0] = Node(p[2].type, p[2].children, p[2].leaf, p[2].defnleaf, node_type=p[2].node_type)

def p_expression_number(p):
		"""
			expression : NUMBER
		"""
		p[0] = Node("CONST", [], p[1], node_type=('int', 0))

def p_expression_fnumber(p):
		"""
			expression : FNUMBER
		"""
		# print(p[1])
		p[0] = Node("CONST", [], p[1], node_type=('float', 0))	

def p_error(p):
	if p:
		errStr = "syntax error at '{0}' line no '%d'".format(p.value) % p.lexer.lineno
	else:
		errStr = "syntax error at EOF"
	printerr(errStr)
	
def process(data):
	lex.lex()
	yacc.yacc()
	yacc.parse(data)

def printerr(errStr):
	print(errStr)
	print_to_output_file_cfg("")
	print_to_output_file_sym()
	print_to_output_file()
	print_to_output_file_asm("Feni")
	sys.exit()

def print_to_output_file():
	f = open(txt_file_name_ast, "w")
	f.write(output_to_txtfile)
	f.close()

def print_to_output_file_cfg(printingthing):
	f = open(txt_file_name_cfg, "w")
	f.write(printingthing)
	f.close()

def print_to_output_file_sym():
	f = open(txt_file_name_sym, "w")
	f.write(printSymTable())
	f.close()

def print_to_output_file_asm(printingthing):
	if printingthing == "Feni":
		return	

	output_to_txtfile_asm = traverseNodeAsm(p0, txt_file_name_cfg)
	f = open(txt_file_name_asm, "w")
	f.write(output_to_txtfile_asm)
	f.close()
	sys.exit()

if __name__ == "__main__":
	global file_name
	file_name = sys.argv[1]

	txt_file_name_ast = file_name+ ".ast"
	txt_file_name_cfg = file_name +".cfg"
	txt_file_name_sym = file_name + ".sym"
	txt_file_name_asm = file_name + ".s"

	with open(file_name, 'r') as f: 
		lines = f.readlines()
	
	data = ''.join(lines)
	process(data)

	print_to_output_file_cfg(output_to_txtfile_cfg)
	print_to_output_file()
	print_to_output_file_sym()
	print_to_output_file_asm(output_to_txtfile_asm)