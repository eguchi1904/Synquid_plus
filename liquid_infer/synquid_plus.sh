#!/bin/sh
# set path to libz3.dylib
export DYLD_LIBRARY_PATH=~/.opam/4.06.1/lib/z3/
INTERMEDIATE_SUFFIX="_2sq.sq"
SQ_EXTENSION=".sq"

SCRIPT_DIR=$(cd $(dirname $0); pwd)
SCRIPT_DIR="${SCRIPT_DIR}/"
SYNQUID_DIR="${SCRIPT_DIR}../synquid/"
OUR_METHOD="our_method"		

# main

input_file=$1
tmp=$2
input_file=$SCRIPT_DIR$input_file
echo "\n\n\n----------------------------------------------------------------------"
time $SCRIPT_DIR$OUR_METHOD $input_file$SQ_EXTENSION "-tmp" $tmp > /dev/null # our method part
echo "----------------------------------------------------------------------\n"

cd $SYNQUID_DIR
time stack exec -- synquid $input_file$INTERMEDIATE_SUFFIX  -f=AllArguments -a=3 -m=2 -e # synquid part


