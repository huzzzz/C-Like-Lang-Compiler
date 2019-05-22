#!/usr/bin/python3
import collections 

global_variable_table = collections.OrderedDict()
global_procedure_table = collections.OrderedDict()
global_defined_yet = {}

heap_regs_d = ['$s'+str(x) for x in range(0,8)] + ['$t'+str(x) for x in range(0,10)]
heap_regs_f = ['$f' + str(x) for x in range(2,32,2)]

width_table = {
	'int' : 4,
	'float' : 8,
}

temp_reg_map = {}
float_cond_no = 0