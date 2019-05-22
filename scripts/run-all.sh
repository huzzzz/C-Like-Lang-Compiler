#!/bin/bash

for i in `seq 0 10`;
        do
            ./test.sh t$i.c
        done  