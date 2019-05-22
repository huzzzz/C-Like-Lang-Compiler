
class Node:
	def __init__(self, type, children=None, leaf=None, defnleaf =None, goto=[], node_type=None):
		 self.type = type
		 if children:
			  self.children = children
		 else:
			  self.children = [ ]
		 self.leaf = leaf
		 self.defnleaf = defnleaf
		 self.goto = goto
		 self.node_type = node_type

class SymTableEntryVar:
	def __init__(self, base_type, loi, offset, width, isParam = False):
		self.base_type = base_type
		self.loi = loi
		self.isParam = isParam
		self.offset = offset
		self.width = width

class SymTableEntryProc:
	def __init__(self, returnType, paramList, width):
		self.returnType = returnType
		self.paramList = paramList
		self.width = width