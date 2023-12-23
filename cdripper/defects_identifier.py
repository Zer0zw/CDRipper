import json
import os
import sys
from func_timeout import func_set_timeout

from slither.slither import Slither
from typing import List, Tuple

from slither.analyses.data_dependency.data_dependency import is_dependent
from slither.core.cfg.node import Node
from slither.core.declarations import Function, Contract, FunctionContract
from slither.core.declarations.solidity_variables import (
    SolidityVariableComposed,
    SolidityVariable,
    SolidityFunction,
)
from slither.core.variables import Variable
from slither.detectors.abstract_detector import (
    AbstractDetector,
    DetectorClassification,
    DETECTOR_INFO,
)
from slither.slithir.operations import Binary, BinaryType
from slither.utils.output import Output

from permission_analysis import getVar_Owner, getVar_Init, getFunc_ChangeOwner

from semantic_analysis import getNode_forSemantic, getFunc_Semantic_fromContract, isNode_dependonExec, isNode_dependonMultisig, isNode_dependonTimelock, get_MainContract

_list_ercfunc_name = [
    # ERC20
    'name()',
    'symbol()',
    'decimals()',
    'totalSupply()',
    'balanceOf(address)',
    'transfer(address,uint256)',
    'transferFrom(address,address,uint256)',
    'approve(address,uint256)',
    'allowance(address,address)',
    # ERC721
    'balanceOf(address)',
    'ownerOf(uint256)',
    'safeTransferFrom(address,address,uint256,bytes)',
    'safeTransferFrom(address,address,uint256)',
    'transferFrom(address,address,uint256)',
    'approve(address,uint256)'
]

def recordMessage(_message, _txt_path):
    # with lock:
    with open(_txt_path, "a") as f:
        f.write(_message + "\n")

def getFunc_2control(_contract: Contract):
    _list_limited_func = []
    _set_limited_func = set()
    _set_limited_node = set()

    _list_owner_var = getVar_Owner(_contract)

    for _func in _contract.functions_and_modifiers:
        if _func.is_constructor == False and _func.is_fallback == False:
            for _node in _func.nodes:
                for _read_var in _node.variables_read:
                    if is_dependent(_read_var, SolidityVariableComposed("msg.sender"), _node):
                        for _owner_var in _list_owner_var:
                            if is_dependent(_read_var, _owner_var, _node):
                                _set_limited_node.add(_node)
                                _set_limited_func.add(_func)
                for _ir in _node.irs:
                    for _read_var in _ir.read:
                        if is_dependent(_read_var, SolidityVariableComposed("msg.sender"), _node):
                            for _owner_var in _list_owner_var:
                                if is_dependent(_read_var, _owner_var, _node):
                                    _set_limited_node.add(_node)
                                    _set_limited_func.add(_func)

    _list_limited_node = sorted(list(_set_limited_node), key = lambda x: x.node_id)
    _list_limited_func = sorted(list(_set_limited_func), key = lambda x: x.name)

    return _list_limited_func, _list_limited_node


def isFunc_limitedbyowner(_function: Function, _list_2control_func):
    _is_satisfied = False

    if _function in _list_2control_func:
        _is_satisfied = True
    else:
        for _node in _function.nodes:
            try:
                for _called_func in _node.internal_calls:
                    if _called_func in _list_2control_func:
                        _is_satisfied = True
            except:
                pass
                        
    return _is_satisfied

def getFunc_limited_public(_contract: Contract):
    _set_limitedpublic_func = set()
    _list_limitedpublic_func = []

    _list_2control_func, _ = getFunc_2control(_contract)

    for _func in _contract.functions:
        if (_func.visibility == 'public') | (_func.visibility == 'external'):
            if (_func.is_constructor == False) and (_func.is_fallback == False):
                if isFunc_limitedbyowner(_func, _list_2control_func):
                    _set_limitedpublic_func.add(_func)
    
    _list_limitedpublic_func = sorted(list(_set_limitedpublic_func), key = lambda x: x.name)

    return _list_limitedpublic_func


def isFunc_withMultisig(_func:Function, _list_dependMultisig_node):
    _exist_mutlisig = False
    for _para in _func.parameters:
        if str(_para.type) == 'bytes':
            _exist_mutlisig = True
            break
    
    if ~_exist_mutlisig:
        return False
    
    for _node in _func.nodes:
        if _node in _list_dependMultisig_node:
            return True
    
    return False

def isFunc_withTimelock(_func:Function, _list_dependTimelock_node):  
    for _node in _func.nodes:
        if _node in _list_dependTimelock_node:
            return True
    
    return False


# ************************************
# Mint Function Control by Single Signature
# ************************************
def getFunc_mint(_contract, _list_limitedpublic_func):
    if _contract.is_token == False:
        return []
    
    _list_mint_func = []
    _set_mint_func = set()
    _list_balances_var = getVar_Balances(_contract)
    
    for _func in _list_limitedpublic_func:
        if (_func.payable == False) and (_func.full_name not in _list_ercfunc_name):
            if isFunc_Mint(_func, _list_balances_var):
                _set_mint_func.add(_func)
            else:
                for _node in _func.nodes:
                    try:
                        for _called_func in _node.internal_calls:
                            if isFunc_Mint(_called_func, _list_balances_var):
                                _set_mint_func.add(_func)
                    except:
                        pass
    
    _list_mint_func = sorted(list(_set_mint_func), key = lambda x: x.name)

    return _list_mint_func

def getVar_Balances(_contract):
    _set_balances_var = set()
    _list_balances_var = []

    for _var in _contract.state_variables:
        if (str(_var.type) == 'mapping(address => uint256)') or (str(_var.type) == 'mapping(address => mapping(address => uint256))'):
            _set_balances_var.add(_var)
    
    _list_balances_var = sorted(list(_set_balances_var), key = lambda x: x.name)

    return _list_balances_var

def isFunc_Mint(_func, _list_balances_var):
    _num_address = 0
    _is_satisfied = False
    _exist_amount = False

    try:
        for _var in _func.variables_read:
            try:
                if _var.type.type == 'address':
                    _num_address += 1  
            except:
                pass
    except:
        pass 

    for _para in _func.parameters:
        if str(_para.type) == 'uint256': 
            _exist_amount = True
   
    try:
        if _num_address == 1 and _exist_amount:
            for _bal_var in _list_balances_var:
                for _node in _func.nodes:
                    if _bal_var in _node.state_variables_written:
                        if '-' not in str(_node) and 'sub' not in str(_node):
                            _is_satisfied = True
                            break
    except:
        pass
        
    return _is_satisfied

# ************************************
# Critical Variables Manipulation by Single Signature
# ************************************
def getFunc_changeCriVar(_contract: Contract, _list_limitedpublic_func):
    _set_changeCriVar_func = set()
    _list_changeCriVar_func = []

    _list_critical_var = getVar_critical(_contract)
    for _func in _list_limitedpublic_func:
        if (_func.full_name not in _list_ercfunc_name):
            if isFunc_changeCriVar(_func, _list_critical_var):
                _set_changeCriVar_func.add(_func) 
            else:
                try:
                    for _node in _func.nodes:
                        for _called_func in _node.internal_calls:
                            if isFunc_changeCriVar(_called_func, _list_critical_var):
                                _set_changeCriVar_func.add(_func)
                except:
                    pass
    _list_changeCriVar_func = sorted(list(_set_changeCriVar_func), key = lambda x: x.name)

    return _list_changeCriVar_func

def getVar_critical(_contract: Contract):
    _set_critical_var = set()
    _list_critical_var = []
    _list_owner_var = getVar_Owner(_contract)

    _list_crinit_var = []
    
    if len(_contract.constructors) > 0:
        for _constructor in _contract.constructors:
            for _var in _constructor.state_variables_written:
                _list_crinit_var.append(_var)
    
    for _var in _list_crinit_var:
        if (_var in _contract.state_variables) and ('address' not in str(_var.type)) and (_var not in _list_owner_var) and ('total' not in str(_var.name).lower()) and ('amount' not in str(_var.name).lower()):
            _set_critical_var.add(_var)
    for _var in _contract.state_variables:
        if ('fee' in str(_var.name).lower()) or ('pause' in str(_var.name).lower()):
            if ('address' not in str(_var.type)):
                _set_critical_var.add(_var)
    _list_critical_var = sorted(list(_set_critical_var), key = lambda x: x.name)

    return _list_critical_var

def isFunc_changeCriVar(_function: Function, _list_critical_var):
    _is_satisfied = False

    for _crivar in _list_critical_var:
        if _crivar in _function.state_variables_written:
            _is_satisfied = True

    return _is_satisfied

# ************************************
# Selfdestruct with single signature
# ************************************
def getFunc_selfdestruct(_contract: Contract, _list_limitedpublic_func):
    _set_selfdestruct_func = set()
    _list_selfdestruct_func = []

    for _func in _list_limitedpublic_func:
        if (_func.full_name not in _list_ercfunc_name):
            for _call in _func.solidity_calls:
                if (_call.name == 'suicide(address)') | (_call.name == 'selfdestruct(address)'):
                    _set_selfdestruct_func.add(_func)
    _list_selfdestruct_func = sorted(list(_set_selfdestruct_func), key = lambda x: x.name)

    return _list_selfdestruct_func

# ************************************
# Single Proxy Admin
# ************************************
def isContract_ProxywithAdmin(_contract: Contract):
    _is_satisfied = False
    if _contract.is_upgradeable_proxy | _contract.is_upgradeable:
        if len(getVar_Owner(_contract)) > 0:
            _is_satisfied = True
    
    return _is_satisfied

# ************************************
# Initial Token Distribution
# ************************************
def isContract_DangerTokenDis(_contract: Contract):
    # 如果合约不是token合约的话，就无所谓token分布的问题了
    if _contract.is_token == False:
        return False
    
    _is_satisfied = False
    _num_tokentransfer_node = 0

    _list_balances_var = getVar_Balances(_contract)
    for _cons in _contract.constructors:
        for _node in _cons.nodes:
            for _bal in _list_balances_var:
                if _bal in _node.state_variables_written:
                    _num_tokentransfer_node += 1
            for _called_func in _node.internal_calls:
                try:
                    for _called_node in _called_func.nodes:
                        for _bal in _list_balances_var:
                            if _bal in _called_node.state_variables_written:
                                _num_tokentransfer_node += 1
                except:
                    pass
        
    if _num_tokentransfer_node == 1:
        _is_satisfied = True

    return _is_satisfied

# ************************************
# Indiviual Contract Output Reliance
# ************************************
def getFunc_relyOutput(_contract: Contract, _list_exec_node, _list_exec_func):
    _set_relyOutput_func = set()
    _list_relyOutput_func = []

    for _func in _contract.functions:
        if _func.full_name not in _list_ercfunc_name:
            _num_call = 0
            for _node in _func.nodes:
                if len(_node.variables_written) > 0:
                    if isNode_dependonExec(_node, _list_exec_node, _list_exec_func):
                        _num_call += 1
                    for _called_func in _node.internal_calls:
                        try:
                            for _called_node in _called_func.nodes:
                                if isNode_dependonExec(_called_node, _list_exec_node, _list_exec_func):
                                    _num_call += 1
                        except:
                            pass
            if _num_call == 1:
                _set_relyOutput_func.add(_func)

    _list_relyOutput_func = sorted(list(_set_relyOutput_func), key = lambda x: x.name)

    return _list_relyOutput_func

def Main_logicAnalysis(_contract_path):
    slither_obj = Slither(_contract_path)
    main_contract = get_MainContract(slither_obj)
    # print('Slither is done')

    exist_Multisig = False
    exist_Timelock = False      

    Dict_LogicAnalysis = {}
    Dict_mint = {
        'risk_mint': False,
        'Mint Function': []
    }
    Dict_crivar = {
        'risk_crivar': False,
        'Crivar Function': []
    }
    Dict_selfdestruct = {
        'risk_selfdestruct': False,
        'Selfdestruct Function': []
    }
    Dict_timelock = {
        'risk_timelock': False,
        'Management Function': []
    }
    Dict_proxy = {
        'risk_proxy': False,
        'Proxy Contracts': []
    }
    Dict_token = {
        'risk_token': False,
        'Token Contract': []
    }
    Dict_output = {
        'risk_relyoutput': False,
        'Rely Output Function': []
    }

    risk_mint = False
    risk_crivar = False
    risk_selfdestruct = False
    risk_timelock = False
    risk_proxy = False
    risk_token = False
    risk_relyoutput = False
    # print('indiviual variables is done')
  
    list_mint_func = []
    list_mannotimelock_func = []
    list_crivar_func = []
    list_selfdestruct_func = []
    list_proxy_con = []
    list_relyoutput_func = []
    list_dangertoken_con = []
    isProxywithAdmin = False

    list_limitedpublic_func = []
    for _func in getFunc_limited_public(main_contract):
        list_limitedpublic_func.append(_func)
    # print('getting limited public func is done!')

    list_timelock_node, list_threshold_node, list_exec_node = getNode_forSemantic(main_contract)
    list_timelock_func = [_node.function for _node in list_timelock_node]
    list_threshold_func = [_node.function for _node in list_threshold_node]
    list_exec_func = [_node.function for _node in list_exec_node]

    set_dependTimelock_node = set()
    set_dependMultisig_node = set()
    for _func in list_limitedpublic_func:
        for _node in _func.nodes:
            if isNode_dependonTimelock(_node, list_timelock_node, list_timelock_func):
                set_dependTimelock_node.add(_node)
            if isNode_dependonMultisig(_node, list_threshold_node, list_threshold_func):
                set_dependMultisig_node.add(_node)
    list_dependTimelock_node = list(set_dependTimelock_node)
    list_dependMultisig_node = list(set_dependMultisig_node)

    list_execTimelock_funcs, list_execMultisig_funcs = getFunc_Semantic_fromContract(main_contract)

    if len(list_execTimelock_funcs) > 0:
        exist_Timelock = True
    if len(list_execMultisig_funcs) > 0:
        exist_Multisig = True

    # detection of Mint Function with Single Signature
    for _func in getFunc_mint(main_contract, list_limitedpublic_func):
        if ~isFunc_withMultisig(_func, list_dependMultisig_node):
            list_mint_func.append(_func)

    # detection of Critical Variables Manipulation by Single Signature and Management without Timelock
    for _func in getFunc_changeCriVar(main_contract, list_limitedpublic_func):
        if ~isFunc_withMultisig(_func, list_dependMultisig_node):
            list_crivar_func.append(_func)
        if ~isFunc_withTimelock(_func, list_dependTimelock_node):
            list_mannotimelock_func.append(_func)

    # detection of Selfdestruct with Single Signature
    for _func in getFunc_selfdestruct(main_contract, list_limitedpublic_func):
        if ~isFunc_withMultisig(_func, list_dependMultisig_node):
            list_selfdestruct_func.append(_func)

    # detection of Single Proxy Admin
    isProxywithAdmin = isContract_ProxywithAdmin(main_contract)
    if isProxywithAdmin:
        list_proxy_con.append(main_contract)

    # detection of Initial Token Distribution
    isDangerTokenDis = isContract_DangerTokenDis(main_contract)          
    if isDangerTokenDis:
        list_dangertoken_con.append(main_contract)

    # detection of Indiviual Contract Output Reliance
    for _func in getFunc_relyOutput(main_contract, list_exec_node, list_exec_func):
        list_relyoutput_func.append(_func)
    # print('contract analysis is done!')

    list_mintfunc_name = [_func.contract.name + '/' + _func.name for _func in list_mint_func]
    list_crivarfunc_name = [_func.contract.name + '/' + _func.name for _func in list_crivar_func]
    list_selfdestruct_name = [_func.contract.name + '/' + _func.name for _func in list_selfdestruct_func]
    list_mannotimelock_name = [_func.contract.name + '/' + _func.name for _func in list_mannotimelock_func]
    list_proxycon_name = [_con.name for _con in list_proxy_con]
    list_dangertokencon_name = [_con.name for _con in list_dangertoken_con]
    list_outputfunc_name = [_func.contract.name + '/' + _func.name for _func in list_relyoutput_func]

        
    if (len(list_mint_func) > 0) & ~exist_Multisig:
        risk_mint = True 
    if (len(list_crivar_func) > 0) & ~exist_Multisig:
        risk_crivar = True
    if (len(list_selfdestruct_func) > 0) & ~exist_Multisig:
        risk_selfdestruct = True
    if (len(list_limitedpublic_func) > 0) & ~exist_Timelock:
        risk_timelock = True
    if isProxywithAdmin & ~exist_Multisig:
        risk_proxy = True
    if isDangerTokenDis:
        risk_token = True
    if len(list_relyoutput_func) > 0:
        risk_relyoutput = True

    Dict_mint['risk_mint'] = risk_mint
    Dict_mint['Mint Function'] = list_mintfunc_name

    Dict_crivar['risk_crivar'] = risk_crivar
    Dict_crivar['Crivar Function'] = list_crivarfunc_name

    Dict_selfdestruct['risk_selfdestruct'] = risk_selfdestruct
    Dict_selfdestruct['Selfdestruct Function'] = list_selfdestruct_name

    Dict_timelock['risk_timelock'] = risk_timelock
    Dict_timelock['Management Function'] = list_mannotimelock_name

    Dict_proxy['risk_proxy'] = risk_proxy
    Dict_proxy['Proxy Contracts'] = list_proxycon_name

    Dict_token['risk_token'] = risk_token
    Dict_token['Token Contract'] = list_dangertokencon_name

    Dict_output['risk_relyoutput'] = risk_relyoutput
    Dict_output['Rely Output Function'] = list_outputfunc_name

    Dict_LogicAnalysis['Mint Function with Single Signature'] = Dict_mint
    Dict_LogicAnalysis['Critical Variables Manipulation with Single Signature'] = Dict_crivar
    Dict_LogicAnalysis['Selfdestruct with Single Signature'] = Dict_selfdestruct
    Dict_LogicAnalysis['Management without Timelock'] = Dict_timelock
    Dict_LogicAnalysis['Single Proxy Admin'] = Dict_proxy
    Dict_LogicAnalysis['Initial Token Distribution'] = Dict_token
    Dict_LogicAnalysis['Indivitual Contract Output Reliance'] = Dict_output

    return Dict_LogicAnalysis


if __name__ == "__main__":
    # path for test
    # contract_path = './examples/0xf4bcc9537e4a6ff9d13a92b6273cc2349b659242.sol'

    # Read the path of target contract
    contract_path = sys.argv[1]
    if not os.path.isabs(contract_path):
        contract_path = os.path.abspath(contract_path)

    # Identify the centralization defects
    dict_CentralDefects = Main_logicAnalysis(contract_path)

    # Output the analysis results
    results_path = './results/' + os.path.splitext(os.path.basename(contract_path))[0] + '.json'
    with open(results_path, 'w') as json_file:
        json.dump(dict_CentralDefects, json_file, indent=4)
    print('The analysis result is stored in ', results_path)

    print('Analysis Finished!')