#!/bin/bash

echo "node.sh starting"

# (e)xit on error, treat (u)nset variable as error
set -eu

TEXT_RESET='\e[0m'
TEXT_RED='\e[0;31m'
TEXT_GREEN='\e[0;32m'
TEXT_YELLOW='\e[0;33m'
TEXT_BLUE='\e[0;34m'
TEXT_MAGENTA='\e[0;35m' # between pink and purple
TEXT_CYAN='\e[0;36m'    # light ugly blue
TEXT_WHITE='\e[0;37m'
TEXT_GREY='\e[0;38m'    # same as reset color it seems


user=$(logname)
PUBLICIP=$(curl icanhazip.com 2> /dev/null)

function writeGreen(){
    echo -e -n "${TEXT_GREEN}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeYellow(){
    echo -e -n "${TEXT_YELLOW}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeRed(){
    echo -e -n "${TEXT_RED}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeBlue(){
    echo -e -n "${TEXT_BLUE}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeMagenta(){                # betwen pink and purple
    echo -e -n "${TEXT_MAGENTA}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeCyan(){
    echo -e -n "${TEXT_CYAN}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeWhite(){
    echo -e -n "${TEXT_WHITE}${1}"
    echo -e -n "${TEXT_RESET}"
}

function writeGrey(){
    echo -e -n "${TEXT_GREY}${1}"
    echo -e -n "${TEXT_RESET}"
}

TEXT_TRY='\e[1;41m'

function writeTry(){
    echo -e -n "${TEXT_TRY}${1}"
    echo -e -n "${TEXT_RESET}"
}

echo "node.sh complete"
