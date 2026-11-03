#!/bin/bash
# Production run: pinned rsieve_v4 at N = 3500, stream B (one of two streams run in parallel).
cd "$(dirname "$0")" || exit 1
./run_sieve.sh p35_10 rsieve_v4 rsieve_v4.c 3500 1125899906842624 1606926912624721 29 16777216 8 || echo FAIL p35_10
./run_sieve.sh p35_08 rsieve_v4 rsieve_v4.c 3500 281474976710656 562949953421312 29 8388608 8 || echo FAIL p35_08
./run_sieve.sh p35_06 rsieve_v4 rsieve_v4.c 3500 70368744177664 140737488355328 29 4194304 8 || echo FAIL p35_06
./run_sieve.sh p35_04 rsieve_v4 rsieve_v4.c 3500 17592186044416 35184372088832 23 2097152 8 || echo FAIL p35_04
./run_sieve.sh p35_02 rsieve_v4 rsieve_v4.c 3500 4398046511104 8796093022208 19 1048576 8 || echo FAIL p35_02
echo P35_B_ALL_DONE
