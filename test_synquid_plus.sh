#!/bin/sh

SCRIPT_DIR=$(cd $(dirname $0); pwd)
TEST_FILE_DIR="sq_files/"

TEST_FILE=(list-intersection
	   list-sub
           list2bin
           fold-sort
           list-rev
           uniq_list
           concat
	   bin2list 
           #merge_sort
           quick_sort)



for file in ${TEST_FILE[@]}
do
    time "${SCRIPT_DIR}/synquid_plus.sh" $TEST_FILE_DIR$file "fold"
done

time "${SCRIPT_DIR}/synquid_plus.sh" "${TEST_FILE_DIR}merge_sort" "merge"

