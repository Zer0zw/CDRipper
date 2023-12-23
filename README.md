# [CDRipper, Definition and Detection of Centralization Defects in Smart Contracts]

**CDRipper** is a Solidity static analysis framework written in Python3. It runs a suite of vulnerability detectors, prints visual information about contract details, and provides an API to easily write custom analyses. Slither enables developers to find vulnerabilities, enhance their code comprehension, and quickly prototype custom analyses.


## Install

### Install Slither
```
python3 setup.py install
```

### Install Libraries
```
pip install -r ./requirements.txt
```

## Usage
```console
python ./cdripper/defects_identifier.py ./examples/0xf4bcc9537e4a6ff9d13a92b6273cc2349b659242.sol
```
