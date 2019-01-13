#!/bin/sh
# set path to libz3.dylib
export DYLD_LIBRARY_PATH=/Users/eguchishingo/.opam/ocaml-base-compiler.4.06.1/lib/z3/
INTERMEDIATE_SUFFIX="_2sq.sq"
SQ_EXTENSION=".sq"

SCRIPT_DIR=$(cd $(dirname $0); pwd)
SCRIPT_DIR="${SCRIPT_DIR}/"
# SYNQUID_DIR="${SCRIPT_DIR}../synquid/"
OUR_METHOD="main"		

# main

input_file=$1

tmp=$2
input_file=$SCRIPT_DIR$input_file 
output_file=$input_file$INTERMEDIATE_SUFFIX
echo "\n\n\n----------------------------------------------------------------------"
time $SCRIPT_DIR$OUR_METHOD $input_file$SQ_EXTENSION "-tmp" $tmp -o $output_file > /dev/null # our method part
echo "----------------------------------------------------------------------\n"

export DYLD_LIBRARY_PATH=
synquid $output_file  -f=AllArguments -a=3 -m=2 -e # synquid part


