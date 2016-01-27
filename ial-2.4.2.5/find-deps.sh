#!/bin/bash

deps=`grep "open import" $1 | sed 's/.*import \([^ ]*\).*/\1.agdai/' | xargs`

echo "${1}i: $1 $deps"
echo