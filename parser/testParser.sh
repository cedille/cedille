#!/bin/sh

dir=$1
parser=`pwd`/CedilleParser
cd $dir
for f in `find -name '*.ced'` ; do
    echo $f: `$parser $f`
done
