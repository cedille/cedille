#!/bin/bash

agda -i src -i gratr-agda -i ~/ial --ghc-flag=-rtsopts -c src/main.agda 
mv src/main cedille
