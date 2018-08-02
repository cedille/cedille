#!/bin/bash

init=
debug=
file=
outputfile="output"

print_help () {
    echo "Cedille Test Help"
    echo "-i | --init            Initialize expected test outputs"
    echo "-f | --file TESTDIR    Run/initialize only specific test"
    echo "-d | --debug           Print debug information"
}

while [ "$1" != "" ]
do
  case $1 in
    -f | --file )  shift
                   file=$1
                   ;;
    -i | --init )  init="1"
                   ;;
    -d | --debug ) debug="1"
                   ;;
    * )            print_help
                   exit 1
  esac
  shift
done

run_test () {
    o=`pwd`
    cd $1
    f=`pwd`
    cd $o

    if [ "$init" == "" ]
    then echo "Executing test $f"
    else echo "Generating test output for $f"
    fi

    if [ "$debug" == "" ]
    then emacs --batch -file $f -l $f/../cedille-mode-tests.el -eval "(cedille-test-init \"$f\" \"$init\")" 2>/dev/null
    else emacs --batch -file $f -l $f/../cedille-mode-tests.el -eval "(cedille-test-init \"$f\" \"$init\")"
    fi

    if [ "$init" != "" ]
    then echo "Done"
    fi
}

echo "Cedille test output from `date`" > $outputfile

if [ "$file" == "" ]
then
  shopt -s nullglob
  for f in ./*.cedtest
  do run_test $f
  done
else 
  run_test $file
fi

echo "Output written to file cedille/cedille-tests/output"
