#!/bin/bash

rm -f libraries

for f in src/cedille.agda-lib gratr-agda/gratr-agda.agda-lib ial/ial.agda-lib ; do
    echo "`pwd`/$f" >> libraries
done
