#!/bin/bash

agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c main.agda 
