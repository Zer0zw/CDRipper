import os
import time
from multiprocessing import Pool, Manager
import random
import warnings

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

from web3 import Web3

from solidity import *


USER_AGENTS = [
    "Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; SV1; AcooBrowser; .NET CLR 1.1.4322; .NET CLR 2.0.50727)",
    "Mozilla/4.0 (compatible; MSIE 7.0; Windows NT 6.0; Acoo Browser; SLCC1; .NET CLR 2.0.50727; Media Center PC 5.0; .NET CLR 3.0.04506)",
    "Mozilla/4.0 (compatible; MSIE 7.0; AOL 9.5; AOLBuild 4337.35; Windows NT 5.1; .NET CLR 1.1.4322; .NET CLR 2.0.50727)",
    "Mozilla/5.0 (Windows; U; MSIE 9.0; Windows NT 9.0; en-US)",
    "Mozilla/5.0 (compatible; MSIE 9.0; Windows NT 6.1; Win64; x64; Trident/5.0; .NET CLR 3.5.30729; .NET CLR 3.0.30729; .NET CLR 2.0.50727; Media Center PC 6.0)",
    "Mozilla/5.0 (compatible; MSIE 8.0; Windows NT 6.0; Trident/4.0; WOW64; Trident/4.0; SLCC2; .NET CLR 2.0.50727; .NET CLR 3.5.30729; .NET CLR 3.0.30729; .NET CLR 1.0.3705; .NET CLR 1.1.4322)",
    "Mozilla/4.0 (compatible; MSIE 7.0b; Windows NT 5.2; .NET CLR 1.1.4322; .NET CLR 2.0.50727; InfoPath.2; .NET CLR 3.0.04506.30)",
    "Mozilla/5.0 (Windows; U; Windows NT 5.1; zh-CN) AppleWebKit/523.15 (KHTML, like Gecko, Safari/419.3) Arora/0.3 (Change: 287 c9dfb30)",
    "Mozilla/5.0 (X11; U; Linux; en-US) AppleWebKit/527+ (KHTML, like Gecko, Safari/419.3) Arora/0.6",
    "Mozilla/5.0 (Windows; U; Windows NT 5.1; en-US; rv:1.8.1.2pre) Gecko/20070215 K-Ninja/2.1.1",
    "Mozilla/5.0 (Windows; U; Windows NT 5.1; zh-CN; rv:1.9) Gecko/20080705 Firefox/3.0 Kapiko/3.0",
    "Mozilla/5.0 (X11; Linux i686; U;) Gecko/20070322 Kazehakase/0.4.5",
    "Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9.0.8) Gecko Fedora/1.9.0.8-1.fc10 Kazehakase/0.5.6",
    "Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/535.11 (KHTML, like Gecko) Chrome/17.0.963.56 Safari/535.11",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_7_3) AppleWebKit/535.20 (KHTML, like Gecko) Chrome/19.0.1036.7 Safari/535.20",
    "Opera/9.80 (Macintosh; Intel Mac OS X 10.6.8; U; fr) Presto/2.9.168 Version/11.52",
]
# the api key is needed!
ETH_KEY = []
send_headers = {
    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/103.0.0.0 Safari/537.36",
    "Connection": "keep-alive",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8",
}

def make_dir(path):
    folders = []
    while not os.path.isdir(path):
        path, suffix = os.path.split(path)
        folders.append(suffix)
    for folder in folders[::-1]:
        path = os.path.join(path, folder)
        os.mkdir(path)

def make_file(path):
    file = os.path.exists(path)
    if not file:
        suffix, filename = os.path.split(path)
        # print(suffix, filename)
        make_dir(suffix)
        os.mknod(path)

def getApi(contract_address, blocknum = "eth", module = "contract", action = "getsourcecode") :
    index = random.randint(1, 1000) % len(ETH_KEY)
    time.sleep(random.random())
    random_agent =  USER_AGENTS[random.randint(0, len(USER_AGENTS)-1)]
    send_headers["User-Agent"] = random_agent
    if module == 'contract':
        if (action == 'getsourcecode') | (action == 'getabi'):
            if blocknum == "eth":
                curl_link = 'https://api.etherscan.io/api?module='+ module +'&action='+ action +'&address=' + \
                                contract_address + \
                                '&apikey=' + ETH_KEY[index]

        elif action == 'getcontractcreation':
            if blocknum == "eth":
                curl_link = 'https://api.etherscan.io/api?module='+ module +'&action='+ action +'&contractaddresses=' + \
                                contract_address + \
                                '&apikey=' + ETH_KEY[index]

    elif module == 'account':
        if (action == 'txlist'):
            if blocknum == "eth":
                curl_link = 'https://api.etherscan.io/api?module='+ module +'&action='+ action +'&address=' + \
                                contract_address + '&startblock=0&endblock=99999999&sort=asc' + \
                                '&apikey=' + ETH_KEY[index]

    print(f"current link: {curl_link}")
    return curl_link

def isAddress_Contract(_address, blockchain = 'eth'):
    _curl_link = getApi(_address, blocknum = blockchain, action = 'getcontractcreation')
    _json_concreation = rq.get(_curl_link, headers=send_headers).json()

    if 'result' in _json_concreation:
        if _json_concreation['result'] == None:
            isContract = False
        else: 
            isContract = True
    else:
        isContract = False
    
    return isContract

def isAddress_VerifiedContract(_address, blockchain = 'eth'):
    is_verifiedCon = True
    is_proxy = False

    _curl_link = getApi(_address, blockchain)
    _rq_source = rq.get(_curl_link, headers = send_headers)
    _json_source = _rq_source.json()

    if 'result' in _json_source:
        _sourcecode = _json_source['result'][0]['SourceCode']
        if len(_sourcecode) == 0:
            if _json_source["result"][0]['ABI'] == "Contract source code not verified" :
                is_verifiedCon = False
            else:
                print('Some Specical Error happened in ', _address)

        _isproxy = _json_source['result'][0]['Proxy']
        if _isproxy == '1':
            is_proxy = True
        else:
            is_proxy = False

    return is_verifiedCon, is_proxy

def isContract_verified_fromjson(json_sourcecode) :
    is_verified = False

    source_code = json_sourcecode["result"][0]["SourceCode"]
    if len(source_code) == 0 :
        if json_sourcecode["result"] == "Contract source code not verified" :
            is_verified = False
        else:
            print("Some Specical Error happened!")
    elif len(source_code) > 0:
        is_verified = True

    return is_verified

def getAddress_Logic(_address, blocknum = "eth") :
    cur_address = _address
    address_logic = _address
    is_proxy = 1
    
    while is_proxy == 1 :
        cur_link = getApi(cur_address, blocknum)
        cur_rq = rq.get(cur_link, headers = send_headers)
        cur_json = cur_rq.json()

        if "result" in cur_json:
            if isContract_verified_fromjson(cur_json):
                is_proxy = int(cur_json["result"][0]["Proxy"])
                if is_proxy == 1:
                    cur_address = cur_json["result"][0]["Implementation"]
                else:
                    address_logic = cur_address
            else:
                print('The contract is not Open Source: ', cur_address)
                break

    return address_logic


def recordMessage(_message, _txt_path):
    with open(_txt_path, "a") as f:
        f.write(_message + "\n")

def is_path(s):
    if s[0] != '/':
        return False
    if '.' in s:
        if '/' in s:
            return True
        else:
            return False
    else:
        if '/' in s:
            return True
        else:
            return False

def get_MainContract(slither_obj):
    _keys = list(slither_obj.crytic_compile.compilation_units.keys())
    _target_contract_name = _keys[0] if len(_keys) == 1 else slither_obj.contracts[-1].name
    if is_path(_target_contract_name):
        _target_contract_name = slither_obj.contracts[-1].name
    for contract in slither_obj.contracts:
        if contract.name == _target_contract_name:
            return contract