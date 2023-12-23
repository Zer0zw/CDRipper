import warnings
# from timeout_decorator import timeout
import time
from func_timeout import func_set_timeout

warnings.filterwarnings("ignore", category=DeprecationWarning)

import requests as rq

from slither.slither import Slither
from typing import List, Tuple

from slither.analyses.data_dependency.data_dependency import is_dependent
from slither.core.cfg.node import Node
from slither.core.declarations import Function, Contract, FunctionContract
from slither.core.declarations.solidity_variables import (
    SolidityVariableComposed,
    SolidityVariable,
)
from slither.core.variables import Variable

from slither.slithir.operations import Binary, BinaryType
from slither.utils.output import Output

import networkx as nx

# a package used to determine the version of solidity
from solidity import *

from cfg_analysis import getContract_Main, getCFG, isNode_dependent
from basic_helper import *


# time limit: 120s
@func_set_timeout(120)
# Function: get the Functions related to the Contract Semantic from Slither Object
def getFunc_Semantic_fromSlither(_slither_obj):
    """
        input: Slither Object
        output: The functions related to MultiSig and Timelock Contracts
                _list_execTimelock_funcs: List of Functions to Execute transactions control by Timelock
                _list_execMultiSig_funcs: List of Functions to Execute transactions control by MultiSig
    """
    # Initialize variables
    _list_execTimelock_funcs = []
    _list_execMultiSig_funcs = []

    # get the main contract from slither object
    _main_contract = getContract_Main(_slither_obj)
    # get the semantic-related functions from main contract
    _list_execTimelock_funcs, _list_execMultiSig_funcs = getFunc_Semantic_fromContract(_main_contract)

    return _list_execTimelock_funcs, _list_execMultiSig_funcs

def getFunc_Semantic_fromContract(_contract: Contract):
    _cfg = getCFG(_contract)

    _list_timelock_node, _list_threshold_node, _list_exec_node = getNode_forSemantic(_contract)
    if len(_list_timelock_node) == 0 and len(_list_threshold_node) == 0 and len(_list_exec_node) == 0:
        return [], []
    
    _list_timelock_func = []
    _list_threshold_func = []
    _list_exec_func = []
    for _node in _list_timelock_node:
        _list_timelock_func.append(_node.function)
    for _node in _list_threshold_node:
        _list_threshold_func.append(_node.function)
    for _node in _list_exec_node:
        _list_exec_func.append(_node.function)

    _set_execTimelock_func = set()
    _set_execMultisig_func = set()

    for _func in _contract.functions:
        _list_timedepend_node = []
        _list_multisigdepend_node = []
        _list_execdepend_node = []
        if (_func.visibility == 'public') | (_func.visibility == 'external'):
            for _node in _func.nodes:
                if isNode_dependonExec(_node, _list_exec_node, _list_exec_func):
                    _list_execdepend_node.append(_node)
                if isNode_dependonMultisig(_node, _list_threshold_node, _list_threshold_func):
                    _list_multisigdepend_node.append(_node)
                if isNode_dependonTimelock(_node, _list_timelock_node, _list_timelock_func):
                    _list_timedepend_node.append(_node)
                
            for _timedepend_node in _list_timedepend_node:
                for _execdepend_node in _list_execdepend_node:
                    if isNode_dependent(_cfg, _execdepend_node, _timedepend_node):
                        _set_execTimelock_func.add(_func)
            
            for _multisigdepend_node in _list_multisigdepend_node:
                for _execdepend_node in _list_execdepend_node:
                    if isNode_dependent(_cfg, _execdepend_node, _multisigdepend_node):
                        _set_execMultisig_func.add(_func)
            

    _list_execTimelock_func = sorted(list(_set_execTimelock_func), key = lambda x: x.name)
    _list_execMultisig_func = sorted(list(_set_execMultisig_func), key = lambda x: x.name)

    return _list_execTimelock_func, _list_execMultisig_func
   
def getNode_forSemantic(_contract: Contract):
    _set_timelock_node = set()
    _set_threshold_node = set()
    _set_exec_node = set()

    _list_threshold_var = getVar_threshold(_contract)
    for _func in _contract.functions:
        for _node in _func.nodes:
            if isNode_forExec(_node):
                _set_exec_node.add(_node)
            if isNode_forThreshold(_node, _list_threshold_var):
                _set_threshold_node.add(_node)
            if isNode_forTimelock(_node):
                _set_timelock_node.add(_node)
    
    _list_timelock_node = sorted(list(_set_timelock_node), key = lambda x: x.node_id)
    _list_threshold_node = sorted(list(_set_threshold_node), key = lambda x: x.node_id)
    _list_exec_node = sorted(list(_set_exec_node), key = lambda x: x.node_id)

    return _list_timelock_node, _list_threshold_node, _list_exec_node

def getVar_threshold(_contract: Contract):
    _set_threshold_var = set()
    if len(_contract.constructors) > 0:
        _constructor = _contract.constructor
        try:
            for _var in _constructor.state_variables_written:
                try:
                    if _var.type.type == 'uint256':
                        _set_threshold_var.add(_var)
                except:
                    pass
        except:
            pass
    else:
        for _var in _contract.state_variables:
            try:
                if _var.type.type == 'uint256':
                    _set_threshold_var.add(_var)
            except:
                pass
    _list_threshold_var = sorted(list(_set_threshold_var), key=lambda x: x.name)
    return _list_threshold_var
    
def isNode_forThreshold(_node: Node, _list_threshold_var):
    for _var in _node.variables_read:
        for _threshold in _list_threshold_var:
            if is_dependent(_var, _threshold, _node):
                return True
    return False

def isNode_forTimelock(_node: Node):
    if _node.contains_require_or_assert():
        for _var in _node.variables_read:
            if is_dependent(_var, SolidityVariableComposed("block.timestamp"), _node):
                return True
            if is_dependent(_var, SolidityVariable("now"), _node):
                return True
    for _ir in _node.irs:
        if isinstance(_ir, Binary) and BinaryType.return_bool(_ir.type):
            for _var_read in _ir.read:
                if not isinstance(_var_read, (Variable, SolidityVariable)):
                    continue
                if is_dependent(_var_read, SolidityVariableComposed("block.timestamp"), _node):
                    return True
                if is_dependent(_var_read, SolidityVariable("now"), _node):
                    return True
    return False

def isNode_forExec(node: Node):
    _use_target = False
    _use_value = False
    _use_data = False
    _use_selfdefine = False

    if len(node.low_level_calls) > 0:
        for _var in node.variables_read:
            try:
                if _var.type.type == 'address':
                    _use_target = True
                elif _var.type.type == 'uint256':
                    _use_value = True
                elif _var.type.type == 'bytes':
                    _use_data = True
                elif str(type(_var.type)) == "<class 'slither.core.solidity_types.user_defined_type.UserDefinedType'>":
                    _use_selfdefine = True
            except:
                pass
        if (_use_target & _use_value & _use_data) or (_use_selfdefine):
            return True

    else:
        try:
            for _called_func in node.internal_calls:
                if (_called_func.name == 'call(uint256,uint256,uint256,uint256,uint256,uint256,uint256)') | (_called_func.name == 'delegatecall(uint256,uint256,uint256,uint256,uint256,uint256)'):
                    for _var in node.variables_read:
                        if _var.type.type == 'address':
                            _use_target = True
                        elif _var.type.type == 'uint256':
                            _use_value = True
                        elif _var.type.type == 'bytes':
                            _use_data = True
                        elif str(type(_var.type)) == "<class 'slither.core.solidity_types.user_defined_type.UserDefinedType'>":
                            _use_selfdefine = True
                    if (_use_target & _use_value & _use_data) or (_use_selfdefine):
                        return True
        except:
            pass 

    return False

def isNode_dependonTimelock(node: Node, _list_time_node, _list_time_func):
    if node in _list_time_node:
        return True
    else:
        _list_called_func = node.internal_calls
        while(len(_list_called_func) > 0):
            _called_func = _list_called_func.pop()
            if _called_func in _list_time_func:
                return True
            else:
                try:
                    for _func in _called_func.internal_calls:
                        _list_called_func.append(_func)
                except:
                    pass
        return False

def isNode_dependonExec(node: Node, _list_exec_node, _list_exec_func):
    if node in _list_exec_node:
        return True
    else:
        _list_calledfunc = node.internal_calls
        while len(_list_calledfunc) > 0:
            _called_func = _list_calledfunc.pop()
            if _called_func in _list_exec_func:
                return True
            else:
                try:
                    for _func in _called_func.internal_calls:
                        _list_calledfunc.append(_func)
                except:
                    pass
        return False

def isNode_dependonMultisig(node: Node, _list_threshold_node, _list_threshold_func):
    # 
    if node in _list_threshold_node:
        return True
    else:
        _list_calledfunc = node.internal_calls
        while len(_list_calledfunc) > 0:
            _called_func = _list_calledfunc.pop()
            if _called_func in _list_threshold_func:
                return True
            else:
                try:
                    for _func in _called_func.internal_calls:
                        _list_calledfunc.append(_func)
                except:
                    pass
        return False

def get_Timelock_node(conc: Contract):
    _set_time_node = set()
    _set_time_func = set()

    for _func in conc.functions:
        for _node in _func.nodes:
            if _node.contains_require_or_assert():
                for _var in _node.variables_read:
                    if is_dependent(_var, SolidityVariableComposed("block.timestamp"), _node):
                        _set_time_node.add(_node)
                        _set_time_func.add(_func)
                    if is_dependent(_var, SolidityVariable("now"), _node):
                        _set_time_node.add(_node)
                        _set_time_func.add(_func)
            for _ir in _node.irs:
                if isinstance(_ir, Binary) and BinaryType.return_bool(_ir.type):
                    for _var_read in _ir.read:
                        if not isinstance(_var_read, (Variable, SolidityVariable)):
                            continue
                        if is_dependent(_var_read, SolidityVariableComposed("block.timestamp"), _node):
                            _set_time_node.add(_node)
                            _set_time_func.add(_func)
                        if is_dependent(_var_read, SolidityVariable("now"), _node):
                            _set_time_node.add(_node)
                            _set_time_func.add(_func)

    _list_time_node = sorted(list(_set_time_node), key=lambda x: x.node_id)
    _list_time_func = sorted(list(_set_time_func), key=lambda x: x.name)

    _list_timenode_name = []
    for _node in _list_time_node:
        _list_timenode_name.append(str(_node.function.name) + '_' + str(_node.node_id))

    return _list_time_node, _list_time_func, _list_timenode_name

def get_SigThreshold_node(conc: Contract):
    _set_threshold_var = set()
    _set_threshold_node = set()
    _set_threshold_func = set()

    _constructor = conc.constructor
    
    try:
        for _var in _constructor.state_variables_written:
            try:
                if _var.type.type == 'uint256':
                    _set_threshold_var.add(_var)
            except:
                pass
    except:
        pass
    _list_threshold_var = sorted(list(_set_threshold_var), key=lambda x: x.name)

    # 寻找依赖threshold的node和function
    for _func in conc.functions:
        for _node in _func.nodes:
            for _var in _node.variables_read:
                for _threshold in _list_threshold_var:
                    if is_dependent(_var, _threshold, _node):
                        _set_threshold_node.add(_node)
                        _set_threshold_func.add(_func)
    _list_threshold_node = sorted(list(_set_threshold_node),  key=lambda x: x.node_id)
    _list_threshold_func = sorted(list(_set_threshold_func),  key=lambda x: x.name)

    _list_threshold_node_name = []
    for _node in _list_threshold_node:
        _list_threshold_node_name.append(str(_node.function.name) + '_' + str(_node.node_id))

    return _list_threshold_node, _list_threshold_func, _list_threshold_node_name

def isFunc_ExecPara(func: Function):
    is_satisfied = False
    _exist_target = False
    _exist_value = False
    _exist_data = False

    for _para in func.parameters:
        try:
            if _para.type.type == 'address':
                _exist_target = True
            elif _para.type.type == 'uint256':
                _exist_value = True
            elif _para.type.type == 'bytes':
                _exist_data = True
        except:
            pass

    if _exist_target and _exist_value and _exist_data:
        is_satisfied = True

    return is_satisfied


