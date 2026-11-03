#!/bin/bash
# Production run: pinned rsieve_v4 at N = 3500, stream A (one of two streams run in parallel).
cd "$(dirname "$0")" || exit 1
./run_sieve.sh p35_09 rsieve_v4 rsieve_v4.c 3500 562949953421312 1125899906842624 29 11863283 8 || echo FAIL p35_09
./run_sieve.sh p35_07 rsieve_v4 rsieve_v4.c 3500 140737488355328 281474976710656 29 5931641 8 || echo FAIL p35_07
./run_sieve.sh p35_05 rsieve_v4 rsieve_v4.c 3500 35184372088832 70368744177664 29 2965820 8 || echo FAIL p35_05
./run_sieve.sh p35_03 rsieve_v4 rsieve_v4.c 3500 8796093022208 17592186044416 23 1482910 8 || echo FAIL p35_03
./run_sieve.sh p35_01 rsieve_v4 rsieve_v4.c 3500 2199023255552 4398046511104 19 741455 8 || echo FAIL p35_01
./run_sieve.sh p35_00 rsieve_v4 rsieve_v4.c 3500 1099511627776 2199023255552 19 524288 8 || echo FAIL p35_00
echo P35_A_ALL_DONE
