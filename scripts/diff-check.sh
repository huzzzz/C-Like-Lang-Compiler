#!/bin/bash

for i in `seq 0 10`;
        do
            diff t$i.c.s ../t$i.c.s
            echo done $i
        done  