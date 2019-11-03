#!/bin/bash

#first argument: # of repetitions
#second argument: tag/name of test

make clean-ial \
&& make clean \
&& make cedille-optimized \
&& make \
&& /usr/bin/time \
     bash -c "{ for i in {1..$1}; do ./cedille-optimized new-lib/stdlib.ced > /dev/null; done; }" \
 > ${2}-${1}x-speed-test.txt 2>&1
