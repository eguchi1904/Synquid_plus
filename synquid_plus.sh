#!/bin/sh
INTERMEDIATE_SUFFIX="_2sq.sq"
SQ_EXTENSION=".sq"
SYNQUID_DIR="../synquid/"
SCRIPT_DIR=$(cd $(dirname $0); pwd)
SCRIPT_DIR="${SCRIPT_DIR}/"
OUR_METHOD="our_method"		

# main

input_file=$1
echo "\n\n\n----------------------------------------------------------------------"
./$OUR_METHOD $input_file$SQ_EXTENSION > /dev/null # our method part
echo "----------------------------------------------------------------------\n"

cd $SYNQUID_DIR
stack exec -- synquid $SCRIPT_DIR$input_file$INTERMEDIATE_SUFFIX # synquid part






