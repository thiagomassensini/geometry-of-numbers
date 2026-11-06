#!/usr/bin/env bash
exec /home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -Dtrace.profiler=true -Dtrace.profiler.threshold=100 "$@"
