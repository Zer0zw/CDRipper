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
from slither.detectors.abstract_detector import (
    AbstractDetector,
    DetectorClassification,
    DETECTOR_INFO,
)
from slither.slithir.operations import Binary, BinaryType
from slither.utils.output import Output

import networkx as nx

from solidity import *

# Function: Determine if a string is a path
def isString_Path(_string):
    """
        input: string
        output: whether the string is a path
    """
    if _string[0] != '/':
        return False
    if '.' in _string:
        if '/' in _string:
            return True
        else:
            return False
    else:
        if '/' in _string:
            return True
        else:
            return False

# Function: get the Main Contract from Slither object
def getContract_Main(_slither_obj):
    """
        input: Slither object
        output: the main contract (Slither.Contract)
    """
    # determine the name of main contract
    _keys = list(_slither_obj.crytic_compile.compilation_units.keys())
    _target_contract_name = _keys[0] if len(_keys) == 1 else _slither_obj.contracts[-1].name
    # if Slither read contracts from local path
    if isString_Path(_target_contract_name):
        _target_contract_name = _slither_obj.contracts[-1].name
    # get the contract with the same name with main contract
    for contract in _slither_obj.contracts:
        if contract.name == _target_contract_name:
            return contract

# Function: get the cfg from contract
def getCFG(_contract: Contract):
    """
        input: contract 
        output: cfg (directed graph)
    """
    _cfg = {}
    for _func in _contract.functions:
        for _node in _func.nodes:
            _cfg[_node] = _node.sons
    # build the direct graph
    _graph = nx.DiGraph(_cfg)
                
    return _graph

# Function: determine if the son node is depend on the father node
def isNode_dependent(graph, _son_node, _father_node, visited=None):
    """
        input: graph: CFG
               _son_node: 
    """
    if visited is None:
        visited = set()

    visited.add(_son_node)

    if _son_node == _father_node:
        return True

    for neighbor in graph.predecessors(_son_node):
        if neighbor not in visited and isNode_dependent(graph, neighbor, _father_node, visited):
            return True

    return False