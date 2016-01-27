#!/bin/bash

CEDILLE=${CEDILLE:-~/cedille/cedille}

cedilleTmp=~/.cedille

mkdir -p $cedilleTmp

pid=$$

logfile=$cedilleTmp/cedille-sh-log-$pid.txt

cleanup() {
  rm -f $logfile
}

trap cleanup EXIT

log() {
  d=`date`
  echo "$d: $1" >> $logfile
}

w=`pwd`
log "An instance of cedille.sh has started (working directory is $w)."

while true ; do
  # get the name of the source file we are supposed to parse
  read sourcefile || exit

  log "Got request to parse $sourcefile"

  # the span file has the same name but ends in .cede
  spanfile="${sourcefile%.ced}.cede"

  # cedille will print out an error if there was a major problem (file not existing, parse error, etc.)
  e=`$CEDILLE +RTS -K1000000000 -RTS $sourcefile`

  if [ "$e" == "" ] ; then
    # print out the span file for the benefit of the emacs mode
    cat "$spanfile"
  else
    echo $e
  fi

  log "Catting back $spanfile"

done

#  if [ $spanfile -ot $sourcefile ] ; then
#
#    log "Span file is out of date, so re-running cedille."

