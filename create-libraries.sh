#!/bin/bash

rm -f libraries

for f in src/cedille.agda-lib ial/ial.agda-lib ; do
    echo "`pwd`/$f" >> libraries
done
