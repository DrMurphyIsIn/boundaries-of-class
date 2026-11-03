#!/bin/bash
# Sieve run wrapper: logs source md5, binary md5, compiler, flags and the exact command, then runs.
#   run_sieve.sh <tag> <binary> <source.c> <N> <A> <A2> <P> <Y> <THREADS>
set -u
tag="$1"; bin="$2"; src="$3"; shift 3
log="runs/$tag.log"; mkdir -p runs
[ -e "$log" ] && { echo "REFUSED: $log exists"; exit 2; }
{
  echo "start $(date)"
  echo "source $src $(md5 -q "$src")"
  echo "binary $bin $(md5 -q "$bin")"
  echo "compiler $(cc --version | head -1)"
  echo "flags cc -O3 -Wall -o $bin $src -lpthread -lm"
  echo "command ./$bin $*"
} > "$log"
/usr/bin/time -l "./$bin" "$@" > "runs/$tag.out" 2> "runs/$tag.err"
rc=$?
{ echo "exit $rc"; grep -v LEFTOVER "runs/$tag.out"; echo "leftover_lines $(grep -c LEFTOVER runs/$tag.out)";
  grep -E " real|maximum resident" "runs/$tag.err"; echo "out_md5 $(md5 -q runs/$tag.out)"; echo "end $(date)"; } >> "$log"
cat "$log"
