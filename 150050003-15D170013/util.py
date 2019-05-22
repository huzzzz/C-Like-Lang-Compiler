from node import Node
from heapq import heappop as pop, heappush as push
from globalVars import *

def getStrForm(tup):
	return tup[0] + " "+ "*" * tup[1]

def getStrForm3(tup):
	return tup[0] + "*" * tup[1]

def getStrForm2(tup):
	return "*" * tup[1] + tup[0]

def modify(p):
	for child in p.children:
		if child.type == "FUNCTION":
			if child.leaf.leaf == 'main':
				temp = child.children[2]
				while len(temp.children) != 0:
					temp = temp.children[1]
				temp.children = [Node("RETURN", [], "return"), Node("SUBBODY", [], "")]
				break

def extractName(Node):
	if Node.type == "VAR" :
		return Node.leaf
	else :
		return extractName(Node.children[0])

def extractDerivedType(Node):
	if Node.type == "VAR" :
		return 0
	temp = extractDerivedType(Node.children[0])
	if Node.type == "ADDR":
		return -1 + temp 
	else :
		return 1 + temp

def getStrDict(paramList):
	temp = dict(paramList)
	for params in temp.keys():
		temp[params] = getStrForm(temp[params])
	return str(temp)

def getList(Node):
	if Node == None :
		return ""
	else :
		templist = []
		for child in Node.children :
			templist.append((child.children[0], (child.children[1], child.children[2])))
		# print(templist)
		return templist

def getStrNormFormArgs(paramList):
	# print(paramList)
	temp = ""
	if (len(paramList) > 0):
		temp += getStrForm(paramList[0][1]) + paramList[0][0]
		for i in range(1, len(paramList)):
			temp += ", " + getStrForm(paramList[i][1]) + paramList[i][0] 
	return temp

def get_loi(Node):
	if Node.type == "DEREF" :
		return get_loi(Node.children[0]) - 1
	elif Node.type == "ADDR":
		return get_loi(Node.children[0]) + 1
	elif Node.type == "VAR":
		return 0

def getStrArg(Node):
	strArgType = []
	for arg in Node.children:
		strArgType.append(arg.leaf)
	return ", ".join(strArgType) 

def get_loi_str(s):
	loi = 0
	for c in s:
		if c == '*':
			loi += 1
		elif c == '&':
			loi -= 1
		else:
			break
	return loi

def extract_name_str(s):
	for i in range(len(s)):
		if s[i] != '*' and s[i] != '&':
			return s[i:]

def free_reg(reg):
	if reg[1] == 'f':
		push(heap_regs_f, reg)
	else:
		push(heap_regs_d, reg)