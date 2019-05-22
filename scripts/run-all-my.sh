#!/bin/bash

for i in `seq 0 10`;
        do
            python3 Parser.py ../t$i.c
        done  