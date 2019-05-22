from util import getStrNormFormArgs, getStrForm2, getList, extractName
from node import Node


empty_list = ["SUBBODY", "DECLARATIONS", "PROG"]

def traverseNodeUtil(Node, tab):
	# print(Node.type)
	# print(Node.leaf)
	output = ""
	if Node.type in empty_list:
		for child in Node.children:
			output = output + traverseNodeUtil(child, tab)
	elif Node.type == "LISTIDS":
		output=""
	elif Node.type == "FUNCTDEC":
		return ""
	elif Node.type == "RETURN":
		tab = tab[0:-2]
		output = output + tab + Node.type + "\n" + tab + "(\n"
		for child in Node.children :
			if child == Node.children[0]:
				output = output + traverseNodeUtil(child, tab + "\t")	
			elif len(Node.children) == 3 and (len(Node.children[2].children) == 0) and child == Node.children[2]:
				output = output + tab + "\n"
				output = output + traverseNodeUtil(child, tab + "\t")
			else :
				output = output + tab + "\t,\n"
				output = output + traverseNodeUtil(child, tab + "\t")
		output = output + tab + ")\n"
	elif Node.type == "FUNCTION":
		if extractName(Node.leaf) == 'main':
			output += "Function " + "Main" + "\n"
		else:
			output += "FUNCTION " + extractName(Node.leaf) + "\n"
		output += "PARAMS (" + getStrNormFormArgs(getList(Node.children[0])) + ")\n"
		output += "RETURNS " + getStrForm2(Node.children[1]) + "\n"
		output += traverseNodeUtil(Node.children[2], tab + "\t") + "\n"
	elif Node.type == "FUNCTCALL":
		output += tab + "CALL " + Node.leaf.split("(")[0] + "(\n"
		temp_list = [traverseNodeUtil(child, tab + "\t") for child in Node.children[0].children]
		output += (tab + "\t,\n").join(temp_list)
		output += tab + ")\n"
	elif len(Node.children) == 0 :
		output = output + tab + Node.type + "(" + Node.leaf + ")" + "\n"		
	else:
		output = output + tab + Node.type + "\n" + tab + "(\n"
		for child in Node.children :
			if child == Node.children[0]:
				output = output + traverseNodeUtil(child, tab + "\t")	
			elif len(Node.children) == 3 and (len(Node.children[2].children) == 0) and child == Node.children[2]:
				output = output + tab + "\n"
				output = output + traverseNodeUtil(child, tab + "\t")
			else :
				output = output + tab + "\t,\n"
				output = output + traverseNodeUtil(child, tab + "\t")
		output = output + tab + ")\n"
	return output

def traverseNode(Node):
	output = "\n"
	output = output + traverseNodeUtil(Node, '')
	return output