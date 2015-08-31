#!/usr/bin/python3

import sys
import re


def Find(pat,text):
    #match = re.search(pat,text)
    match = re.findall(pat,text)
    if match: print(match)
    else: print('not found')

def main():
    Find('(\w[\w.]*)@([\w.]+)','blah .nick.p@gmail.com yatta foo@bar ')





if __name__ == '__main__':
    main()

