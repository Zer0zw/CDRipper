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


def getVar_Owner(conc: Contract):
    _set_owner_var = set()
    _list_filtered_var = []

    _list_init_var = getVar_Init(conc)
    for _var in _list_init_var:
        if "address" in str(_var.type):
            if (not str(_var.type) == 'mapping(address => uint256)') and (not str(_var.type) == 'mapping(address => mapping(address => uint256))'):
                if not str(_var.name) == 'uniswapV2Pair':
                    _list_filtered_var.append(_var)

    for _func in conc.functions:
        for _node in _func.nodes:
            for _var in _node.variables_read:
                if is_dependent(_var, SolidityVariableComposed("msg.sender"), _node):
                    for _init_var in _list_filtered_var:
                        if is_dependent(_var, _init_var, _node):
                            _set_owner_var.add(_init_var)
            for _ir in _node.irs:
                for _var_read in _ir.read:
                    if is_dependent(_var_read, SolidityVariableComposed("msg.sender"), _node):
                        for _init_var in _list_filtered_var:
                            if is_dependent(_var_read, _init_var, _node):
                                _set_owner_var.add(_init_var)
    
    _list_owner_var = sorted(list(_set_owner_var), key=lambda x: x.name)
    return _list_owner_var

def getVar_Init(conc: Contract):
    _set_init_var = set()
    _list_constructors = []
    if len(conc.constructors) > 0:
        _list_constructors = conc.constructors
    for _func in conc.functions:
        if str(_func.name).find("init"):
            _list_constructors.append(_func)

    if len(_list_constructors) == 0:
        return []

    for _constructor in _list_constructors:
        try: 
            for _node in _constructor.nodes:
                for _var in _node.state_variables_written:
                    _set_init_var.add(_var)
                for _called_func in _node.internal_calls:
                    for _called_node in _called_func.nodes:
                        for _called_var in _called_node.state_variables_written:
                            _set_init_var.add(_called_var)
        except:
            pass
    _list_init_var = sorted(list(_set_init_var), key=lambda x: x.name)

    return _list_init_var

def getFunc_ChangeOwner(conc: Contract, _list_owner_var):
    _set_changeowner_func = set()
    _dict_type = {}

    for _func in conc.functions:
        _is_callable, _para_type = getType_ChangeOwner(_func)
        
        if _is_callable == 1:

            for _var in _func.state_variables_written:
                if _var in _list_owner_var:
                    _set_changeowner_func.add(_func)
                    _dict_type[_func.name] = _para_type

            try:
                for _called_func in _func.internal_calls:
                    for _var in _called_func.state_variables_written:
                        if _var in _list_owner_var:
                            _set_changeowner_func.add(_func)
                            _dict_type[_func.name] = _para_type
            except:
                pass

            for _node in _func.nodes:
                try:
                    for _called_func in _node.internal_calls:
                        for _called_node in _called_func.nodes:
                            for _called_var in _called_node.state_variables_written:
                                if _called_var in _list_owner_var:
                                    _set_changeowner_func.add(_func)
                                    _dict_type[_func.name] = _para_type
                except:
                    pass

    _list_changeowner_func = sorted(list(_set_changeowner_func), key = lambda x: x.name)

    return _list_changeowner_func, _dict_type

def getType_ChangeOwner(func: Function):
    _is_callable = 0
    _paratype = 'None'

    if ((func.is_constructor == False) & (func.visibility == 'public')) | ((func.is_constructor == False) & (func.visibility == 'external')):
        for para in func.parameters:
            if para.type.type == 'address':
                _is_callable = 1
                _paratype = 'address'
        for read_var in func.variables_read:
            if read_var == SolidityVariableComposed("msg.sender"):
                _is_callable = 1
                _paratype = 'msgsender'

    return _is_callable, _paratype