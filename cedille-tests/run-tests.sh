#!/bin/bash

init=
file=
errmsg="Use --init to generate expected test outputs and --file TESTDIR to run only a specific test"

while [ "$1" != "" ]
do
  case $1 in
    -f | --file )  shift
                   file=$1
                   ;;
    -i | --init )  init="1"
                   ;;
    * )            echo $errmsg
                   exit 1
  esac
  shift
done

run_test () {
    o=`pwd`
    cd $1
    f=`pwd`
    cd $o
    if [ "$2" == "" ]
    then echo "Executing test $f"
    else echo "Generating test output for $f"
    fi
    emacs --batch -file $f -l $f/../cedille-mode-tests.el -eval "(init-test \"$f\" \"$2\")"
    if [ "$2" != "" ]
    then echo "Done"
    fi
}

if [ "$file" == "" ]
then
  shopt -s nullglob
  for f in ./*.cedtest
  do run_test $f $init
  done
else 
  run_test $file $init
fi
