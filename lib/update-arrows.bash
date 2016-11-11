#!/bin/sh

INPUT="$1"

if [[ -f $INPUT ]]; then
    sed -i 's/⇐/◂/g' $INPUT
    sed -i 's/→/➔/g' $INPUT
    echo "Updated all arrows in file $INPUT"
elif [[ -d $INPUT ]]; then
    for FILE in $INPUT/*.ced; do
	sed -i 's/⇐/◂/g' $FILE
	sed -i 's/→/➔/g' $FILE
	echo "Updated all arrows in file $FILE"
    done
else
    echo "'$INPUT' is not a valid file or directory"
    exit 1
fi
