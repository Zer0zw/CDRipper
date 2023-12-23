import json
import os
import sys
import re
from multiprocessing import Pool, Manager
import warnings
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
from slither.detectors.abstract_detector import (
    AbstractDetector,
    DetectorClassification,
    DETECTOR_INFO,
)
from slither.slithir.operations import Binary, BinaryType
from slither.utils.output import Output

import networkx as nx

from solidity import *

from web3 import Web3

from permission_analysis import getVar_Owner, getFunc_ChangeOwner
from semantic_analysis import getFunc_Semantic_fromSlither
from basic_helper import *

def getPermissionChain(_input_address):
    blockchain = 'eth'

    print('Strating to analysis contract: ', _input_address)

    Dict_BasicInformation = { 
        'InputAddress': None,  
        'isContract': False,  
        'IsVerifiedContract': False,  
        'IsProxy': False,  
        'LogicAddress': None,  
        'ExistTimelock': False,  
        'ExistMultisig': False  
    }
    List_RelatedContracts_Info = []
    Dict_RelatedContract_Info = { 
        'Address': None,  
        'IsProxy': False,  
        'ProxyAddress': None,  
        'IsMultiSig': False,  
        'IsTimelock': False,  
        'IsInputLogic': False,  
        'PermissionRoles': [],  
        'PermissionTransferTransactions': []  
    }

    # print('Start to analysis the Basic Information...')
    isContract = isAddress_Contract(_input_address, blockchain = 'eth')
    if isContract == False:
        raise Exception("Address" , _input_address, "is not a Contract!")
    
    is_verifiedCon_input, is_proxy = isAddress_VerifiedContract(_input_address, blockchain = 'eth')
    
    if is_verifiedCon_input == False:
        raise Exception("Contract" , _input_address, "is not verified!")
    else:
        address_logic = getAddress_Logic(_input_address, blockchain)
    
    Dict_BasicInformation['InputAddress'] = _input_address
    Dict_BasicInformation['isContract'] = isContract
    Dict_BasicInformation['IsVerifiedContract'] = is_verifiedCon_input
    Dict_BasicInformation['IsProxy'] = is_proxy
    Dict_BasicInformation['LogicAddress'] = address_logic
    
    # print('Basic Information analysis is finished!')

    list_address2analysis = []
    list_address2analysis.append(address_logic)
    list_analyzed_address = []
    is_inputaddress = True

    # print('Start to analysis the Ownerchain...')

    while (len(list_address2analysis) > 0):
        Dict_RelatedContract_Info = { 
            'Address': None,  
            'IsProxy': False,  
            'ProxyAddress': None,  
            'IsMultiSig': False,  
            'IsTimelock': False, 
            'IsInputLogic': False,  
            'PermissionRoles': [],  
            'PermissionTransferTransactions': []  
        }

        address2analysis = list_address2analysis.pop(0)
        Dict_RelatedContract_Info['ProxyAddress'] = address2analysis
        Dict_RelatedContract_Info['IsInputLogic'] = is_inputaddress
        is_inputaddress = False

        # print('Start to analysis address: ', address2analysis)
        # print('Start to analysis the contract source code...')
        _is_verifiedCon, _is_proxy = isAddress_VerifiedContract(address2analysis, blockchain = 'eth')
        Dict_RelatedContract_Info['IsProxy'] = _is_proxy

        if _is_verifiedCon == False:
            List_RelatedContracts_Info.append(Dict_RelatedContract_Info)
            list_analyzed_address.append(address2analysis)
            continue
        else:
            _curl_link = getApi(address2analysis, blocknum = blockchain)
            _json_source = rq.get(_curl_link, headers=send_headers).json()

            _logicaddress2analysis = getAddress_Logic(address2analysis, blockchain)
            list_analyzed_address.append(address2analysis)
            Dict_RelatedContract_Info['Address'] = _logicaddress2analysis

            slither_obj = Slither(_logicaddress2analysis)
            main_contract = get_MainContract(slither_obj)

            _list_execMultisig_funcs, _list_execTimelock_funcs = getFunc_Semantic_fromSlither(slither_obj)
            if len(_list_execMultisig_funcs) > 0:
                Dict_RelatedContract_Info['IsMultiSig'] = True
            if len(_list_execTimelock_funcs) > 0: 
                Dict_RelatedContract_Info['IsTimelock'] = True

            _list_owner_vars = getVar_Owner(main_contract)
            _list_owner_funcs, _dict_ownerfuncs_type = getFunc_ChangeOwner(main_contract, _list_owner_vars)           
            
            list_ownerfuncs_name = []
            for _func in _list_owner_funcs:
                list_ownerfuncs_name.append(_func.name)

            # print('Start to analysis the transactions...')
            _list_owner_address, _list_transhash = getAddress_Owner(_logicaddress2analysis, _list_owner_funcs, list_ownerfuncs_name, _dict_ownerfuncs_type)

            Dict_RelatedContract_Info['PermissionRoles'] = _list_owner_address
            Dict_RelatedContract_Info['PermissionTransferTransactions'] = _list_transhash
            List_RelatedContracts_Info.append(Dict_RelatedContract_Info)
            if _logicaddress2analysis not in list_analyzed_address:
                list_analyzed_address.append(_logicaddress2analysis)

            for _address in _list_owner_address:
                if _address not in list_analyzed_address:
                    list_address2analysis.append(_address)

    for _dict in List_RelatedContracts_Info:
        if _dict['IsMultiSig']:
            Dict_BasicInformation['ExistMultisig'] = True
        if _dict['IsTimelock']:
            Dict_BasicInformation['ExistTimelock'] = True
        
    # print('Finished! contract: ', _input_address)  

    Dict_AllInformation = {}
    Dict_AllInformation['Basic_Information'] = Dict_BasicInformation
    Dict_AllInformation['RelatedContract_Information'] = List_RelatedContracts_Info
    _dict_json = json.dumps(Dict_AllInformation)

    return _dict_json

    
def getAddress_Owner(
        _con_address, 
        _list_ownerfuncs,
        _list_ownerfuncs_name, 
        _dict_ownerfuncs_type
    ):
    
    _count_trans = 0
    _list_owner_address = []
    _list_of_transhash = []
    w3 = Web3()
    _dict_newest_owner = {}

    _list_trans = getTrans_fromAddress(_con_address)
    # print('the transactions crawling is finished!')
    
    _pattern = r'^([^(]+)\('
    for _tran in _list_trans:
        _count_trans += 1
        _search_result = re.search(_pattern, str(_tran['functionName']))
        if _search_result != None:
            _calledfunc_name = _search_result.group(1)
            for i in range(len(_list_ownerfuncs_name)):
                if _calledfunc_name == _list_ownerfuncs_name[i]:
                    _called_func = _list_ownerfuncs[i]
                    _para_type = _dict_ownerfuncs_type[_called_func.name]

                    if _para_type == 'address':
                        _link_conabi = getApi(_con_address, action = 'getabi')
                        _json_conabi = rq.get(_link_conabi, headers = send_headers).json()
     
                        _contract_w3 = w3.eth.contract(address = _con_address, abi = _json_conabi['result'])
                        _func_w3, _paras = _contract_w3.decode_function_input(_tran['input'])
                        for _value in _paras.values():
                            if isStr_Address(_value):
                                _address_newowner = _value
                                break

                    elif _para_type == 'msgsender':
                        _address_newowner = _tran['from']

                    _dict_newest_owner[_called_func.name] = _address_newowner
                    _list_of_transhash.append(_tran['hash'])

    for _value in _dict_newest_owner.values():
        _list_owner_address.append(_value)

    if len(_list_owner_address) == 0:
        _creator_address = getAddress_creator(_con_address)
        _list_owner_address.append(_creator_address)
    
    # print(_count_trans, 'transactions has been analized!')

    return _list_owner_address, _list_of_transhash

def getAddress_creator(_address):
    creator_address = '0x0'

    _curl_link = getApi(_address, action = 'getcontractcreation')
    _cur_rq = rq.get(_curl_link, headers = send_headers)
    _cur_json = _cur_rq.json()

    creator_address = _cur_json["result"][0]["contractCreator"]

    return creator_address

def getTrans_fromAddress(_address):
    list_trans = []

    _curl_link = getApi(_address, module = 'account', action = 'txlist')
    _cur_rq = rq.get(_curl_link, headers = send_headers)
    _cur_json = _cur_rq.json()

    list_trans = _cur_json["result"]

    return list_trans

def isStr_Address(_string):
    if len(_string) != 42:
        return False
    if _string[:2] != '0x':
        return False
    return True



if __name__ == "__main__":
    # address for test
    # input_address = '0x1d8ba59405fdb67d2f73b48e31296e00f2d5d339'

    # Read the input address
    input_address = sys.argv[1]

    # Cross-Contract Analysis
    Dict_PermissionChain = getPermissionChain(input_address)

    # Output the analysis results
    results_path = './results/cross-contract_analysis/' + os.path.splitext(os.path.basename(input_address))[0] + '.json'
    with open(results_path, 'w') as json_file:
        json.dump(Dict_PermissionChain, json_file, indent=4)
    print('The cross-contract analysis result is stored in ', results_path)
    
    print('Analysis Finished!')