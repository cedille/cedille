#!/usr/bin/env bash
# to be run in docs/src/ because of the relative path

{ echo '@node changelog,credits,roadmap,Top'
  echo '@include version.texi'
  echo '@chapter Change Log'
  cat ../../CHANGELOG.md \
  | sed 's/^# \(.*\)$/@end itemize\n@section \1\n@itemize/' \
  | sed 's/^- /@item /' \
  | tail -n +2
  echo '@end itemize'
} > ./changelog.texi

makeinfo -o ../info/cedille-info-main.info cedille-info-main.texi

# for later, generating more forms of the documentation

makeinfo -o ../html --html cedille-info-main.texi

# texi2pdf -o ../pdf/Cedille-info-main.pdf cedille-main.texi
