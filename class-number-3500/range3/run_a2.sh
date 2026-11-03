#!/bin/bash
# Reproduction run: pinned rsieve_v4 at N = 3000 on all eleven Table-3 intervals (reproduces Jaswal's counts).
cd "$(dirname "$0")" || exit 1
./run_sieve.sh a2_02 rsieve_v4 rsieve_v4.c 3000 4398046511104 8796093022208 19 1048576 8 || echo FAIL a2_02
./run_sieve.sh a2_03 rsieve_v4 rsieve_v4.c 3000 8796093022208 17592186044416 23 1482910 8 || echo FAIL a2_03
./run_sieve.sh a2_04 rsieve_v4 rsieve_v4.c 3000 17592186044416 35184372088832 23 2097152 8 || echo FAIL a2_04
./run_sieve.sh a2_05 rsieve_v4 rsieve_v4.c 3000 35184372088832 70368744177664 29 2965820 8 || echo FAIL a2_05
./run_sieve.sh a2_06 rsieve_v4 rsieve_v4.c 3000 70368744177664 140737488355328 29 4194304 8 || echo FAIL a2_06
./run_sieve.sh a2_07 rsieve_v4 rsieve_v4.c 3000 140737488355328 281474976710656 29 5931641 8 || echo FAIL a2_07
./run_sieve.sh a2_08 rsieve_v4 rsieve_v4.c 3000 281474976710656 562949953421312 29 8388608 8 || echo FAIL a2_08
./run_sieve.sh a2_09 rsieve_v4 rsieve_v4.c 3000 562949953421312 1125899906842624 29 11863283 8 || echo FAIL a2_09
./run_sieve.sh a2_10 rsieve_v4 rsieve_v4.c 3000 1125899906842624 1606926912624721 29 16777216 8 || echo FAIL a2_10
./run_sieve.sh a2_00 rsieve_v4 rsieve_v4.c 3000 1099511627776 2199023255552 19 524288 8 || echo FAIL a2_00
./run_sieve.sh a2_01 rsieve_v4 rsieve_v4.c 3000 2199023255552 4398046511104 19 741455 8 || echo FAIL a2_01
echo A2_ALL_DONE
