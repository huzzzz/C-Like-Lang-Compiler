from util import extractName, getList, getStrNormFormArgs
from node import Node

bbc = 0

def block_nums(Node, asgnFlag = False) :
	global bbc
	# print(Node.type)
	if Node.type == "SUBBODY":

		if len(Node.children) == 0 :
			Node.leaf = str(bbc)
			return
		
		if Node.children[0].type == 'DECLARATIONS' :
			pass
		
		elif Node.children[0].type == 'ASGN' :
			if asgnFlag == False :
				Node.leaf = str(bbc)
				bbc += 1
				asgnFlag = True
		
		elif Node.children[0].type == 'IF' :
			asgnFlag = False
			Node.leaf = str(bbc)
			bbc += 1
			block_nums(Node.children[0].children[1])

			if len(Node.children[0].children) == 3 :
				block_nums(Node.children[0].children[2])
		
		elif Node.children[0].type == 'WHILE' :
			asgnFlag = False

			Node.leaf = str(bbc)
			bbc += 1
			block_nums(Node.children[0].children[1])

		elif Node.children[0].type == 'RETURN' :
			# print("JA RAHA HAI")
			asgnFlag = False
			Node.leaf = str(bbc)
			bbc += 1
		
		elif Node.children[0].type == 'FUNCTCALL' :
			if asgnFlag == False :
				Node.leaf = str(bbc)
				bbc += 1
				asgnFlag = True
		
		block_nums(Node.children[1], asgnFlag)
	elif Node.type == "FUNCTION":
		block_nums(Node.children[2], asgnFlag)
	elif Node.type == "PROG":
		for child in Node.children:
			block_nums(child, asgnFlag)


def goto_nums(Node, defaultgoto):
	# print(Node.type)
	if Node.type == "SUBBODY":
		if len(Node.children) == 0:
			# print("!!! YAHAN AANA CHAHIYE")
			Node.goto = [defaultgoto]	
			return

		elif Node.children[0].type == "ASGN" or Node.children[0].type == "FUNCTCALL":		
			if len(Node.children[1].children)== 0:
				Node.goto = [defaultgoto]
				# print("YAHAN AANA CHAHIYE", Node.children[0].leaf)
				goto_nums(Node.children[1], defaultgoto)
			elif Node.children[1].children[0].type == "ASGN" or Node.children[1].children[0].type == "FUNCTCALL":
				Node.goto = []
				# print("! YAHAN AANA CHAHIYE")
			else:
				# print("!! YAHAN AANA CHAHIYE")
				# print(Node.children[1].leaf)	
				Node.goto = [Node.children[1].leaf]
			goto_nums(Node.children[1], defaultgoto)

		elif Node.children[0].type == "IF":
			newdef = ""
			if len(Node.children[1].children) == 0 :
				newdef = defaultgoto
			else :
				newdef = Node.children[1].leaf
			if Node.children[0].children[2].children == []:

				if (Node.children[0].children[1] == ""):
					Node.goto = [Node.children[1].leaf] * 2
				else:
					Node.goto = [Node.children[0].children[1].leaf, newdef]
					goto_nums(Node.children[0].children[1], newdef)

				goto_nums(Node.children[1], defaultgoto)
				
			elif len(Node.children[0].children) == 3:
				goto_nums(Node.children[0].children[1], newdef)
				if (Node.children[0].children[2]==""):
					Node.goto = [Node.children[0].children[1].leaf, Node.children[1].leaf]
				else:
					Node.goto = [Node.children[0].children[1].leaf, Node.children[0].children[2].leaf]
					goto_nums(Node.children[0].children[2], newdef)
				goto_nums(Node.children[1], defaultgoto)
		
		elif Node.children[0].type == "WHILE":
			newdef = ""
			if len(Node.children[1].children) == 0 :
				newdef = defaultgoto
			else :
				newdef = Node.children[1].leaf
			if len(Node.children[0].children) == 2:
				if (Node.children[0].children[1] == ""):
					Node.goto = [newdef] * 2
				else:
					Node.goto = [Node.children[0].children[1].leaf, newdef]
					goto_nums(Node.children[0].children[1], Node.leaf)

				goto_nums(Node.children[1], defaultgoto)
			
		else:
			goto_nums(Node.children[1], defaultgoto)

	elif Node.type == "FUNCTION":
		goto_nums(Node.children[2], defaultgoto)
	elif Node.type == "PROG":
		for child in Node.children:
			goto_nums(child, defaultgoto)


def traverseNodeCfg(Node):
	output = "\n"
	global bbc
	block_nums(Node)
	goto_nums(Node, str(bbc))
	output = output + printCfgUtil(Node)
	return output

def printCfgUtil(Node) :
	output = ""
	if Node.type == 'SUBBODY':	
		# print("Node.leaf",Node.leaf)
		# print(len(Node.children))
		if len(Node.children) == 0:
			if len(Node.goto) == 0:
				return output
		elif Node.leaf == "" :
			if Node.children[0].type == 'ASGN' :
				# print("ELIF me gaya")
				output += print_with_leafdefs(Node.children[0])
				output += Node.children[0].leaf + "\n"

			elif Node.children[0].type == 'FUNCTCALL':
				# print("Neech")

				output += print_with_leafdefs(Node.children[0])
				output += Node.children[0].leaf + "\n"

			if len(Node.goto) > 0:
				output += "goto <bb "+Node.goto[0]+">\n\n"
			output += printCfgUtil(Node.children[1])
		
		else :
			output += "<bb " + Node.leaf + ">\n"
			if Node.children[0].type == 'ASGN' or Node.children[0].type == 'FUNCTCALL' :
				# print("ELSE me gaya")
				output += print_with_leafdefs(Node.children[0])
				output += Node.children[0].leaf + "\n"
				# print("Node.goto", Node.goto)
				if len(Node.goto) > 0:
					# print('GD',Node.goto)
					output += "goto <bb "+Node.goto[0]+">\n\n"
				output += printCfgUtil(Node.children[1]) 
			elif Node.children[0].type == 'DECLARATIONS':
				output += printCfgUtil(Node.children[1]) 
			elif Node.children[0].type == 'RETURN':
				if len(Node.children[0].children) != 0:
					# print(Node.children[0])
					output += print_with_leafdefs(Node.children[0].children[0])
					output += "return " + Node.children[0].children[0].leaf
				else:
					output += "return "
				output += "\n\n"
			else:
				output += print_with_leafdefs(Node.children[0].children[0])
				# print(Node.goto)
				if (len(Node.goto) == 2):
					output += "if("+Node.children[0].children[0].leaf+") goto <bb "+Node.goto[0]+">\n"
					output += "else goto <bb "+Node.goto[1]+">\n\n"
					output += printCfgUtil(Node.children[0].children[1])
					if len(Node.children[0].children) == 3:		
						output += printCfgUtil(Node.children[0].children[2])
					output += printCfgUtil(Node.children[1])
	elif Node.type == "FUNCTION":
		if extractName(Node.leaf) == "Main":
			output += "function main" + "()\n"
		else:
			output += "function " + extractName(Node.leaf) + "("+getStrNormFormArgs(getList(Node.children[0]))+")\n"
		output += printCfgUtil(Node.children[2])
	elif Node.type == "PROG":
		for child in Node.children:
			output += printCfgUtil(child)
	return output


def print_with_leafdefs(Node):
	output = ""
	# print("Node.defnleaf", Node.defnleaf)
	for child in Node.children:
		output += print_with_leafdefs(child)
	if Node.defnleaf != None:
		output += Node.defnleaf	+ "\n"
	# print(output)
	return output