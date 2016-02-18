#!/bin/sh

if test $# = 0; then
    echo "usage: $0 <file prefix>"
    exit 1
fi

TEST=`basename $1`
ERROR=0

# List of program to run
RUN="prog1 prog2"
# Program arguments. Could be empty.
ARGS="-arg1 -arg2 -o file1 ${TEST}.ml"
# Logs or other outputs to check
CHECKS="some.log other.ml"

# Check if all executables are present
for i in ${RUN}; do
    if [ ! -x ${i} ]; then
	echo "File ${i} does not exist or not executable"
	ERROR=$((${ERROR} + 1))
    fi
done

if [ ${ERROR} -gt 0 ]; then
    exit ${ERROR}
fi

# Add current dir to search path
OLDPATH=${PATH}
PATH=.:${PATH}

for i in ${RUN}; do
    log=`basename ${i}`
    ${i} ${ARGS} > ${log}.log
done

# Restore search path
PATH=${OLDPATH}

# Compare check outputs to saved samples
for i in ${CHECKS}; do
    if ! diff -u orig/${i} ${i} > ${i}.diff; then
	echo "${TEST}: FAILED (see ${i}.diff)"
	ERROR=$((${ERROR} + 1))
    else
	rm -f ${i}.diff
    fi
done

if [ ${ERROR} -eq 0 ]; then
    #echo "${TEST}: passed"
    exit 0
else
    exit ${ERROR}
fi
