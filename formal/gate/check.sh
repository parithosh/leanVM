#!/usr/bin/env bash
# The proof gate for one Lean project, run on its build (`lake build` first):
#
#   formal/gate/check.sh [--update] <project dir> <headline theorem>...
#
# `Gate.lean`, in one process that runs none of the project's code, replays every module
# the project's sources import (closure decided by where each `.olean` lies, not by a file
# listing) through the kernel, checks every one of their constants' axioms from the
# replayed terms, and prints what the headline theorems state. That, digested one line per
# constant, with each headline's axioms and the toolchain and dependency pins in plain text,
# must equal the project's committed `statements.txt`: a change to a statement is a change
# to that file, visible in review. `--update` rewrites it.
#
# Trusted, not replayed: the toolchain and the git dependencies `lake-manifest.json` pins
# (Mathlib, VCVio, ...). A path dependency is refused. Nothing here runs `lake`, so no
# project code runs; code that ran at build time and wrote into a trusted directory is
# outside what the gate can see, which is why CI runs it in a job of its own, on the
# project's build output alone.
#
# GATE_DIR names another copy of formal/gate to run (CI runs the base revision's).
set -euo pipefail

gate="${GATE_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
update=0
if [ "${1:-}" = "--update" ]; then
  update=1
  shift
fi
cd "$1"
shift
if [ "$#" = 0 ]; then
  echo "name at least one headline theorem" >&2
  exit 2
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

toolchain="$(tr -d '[:space:]' <lean-toolchain)"
if ! [[ "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo "lean-toolchain must name a leanprover/lean4 release, got '$toolchain'" >&2
  exit 1
fi
if [ -e lakefile.lean ]; then
  echo "lakefile.lean runs code; the gate takes a lakefile.toml project" >&2
  exit 1
fi
if [ -n "$(find .lake/build ! -type f ! -type d 2>/dev/null)" ]; then
  echo "the build directory holds symlinks or other files that are neither files nor directories:" >&2
  find .lake/build ! -type f ! -type d >&2
  exit 1
fi
lean="$(elan which lean)"
libdir="$(dirname "$(dirname "$lean")")/lib/lean"

# The pins, in plain text, and the build directories they make trusted.
python3 - "$tmp/pins.txt" "$tmp/trusted.txt" "$toolchain" <<'EOF'
import json, os, re, sys
pins, trusted, toolchain = sys.argv[1:]
packages = json.load(open('lake-manifest.json'))['packages'] if os.path.exists('lake-manifest.json') else []
with open(pins, 'w') as out, open(trusted, 'w') as dirs:
    print(f'toolchain {toolchain}', file=out)
    packages_dir = os.path.realpath('.lake/packages')
    for p in sorted(packages, key=lambda p: p['name']):
        name = p['name']
        if p.get('type') != 'git':
            sys.exit(f"dependency {name} is a {p.get('type')} package: only pinned git ones are trusted")
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or not p['url'].startswith('https://github.com/'):
            sys.exit(f"dependency {name} ({p['url']}) must be a plain name hosted on github.com")
        print(f"package {name} {p['url']} {p['rev']}", file=out)
        build = f".lake/packages/{name}/.lake/build/lib/lean"
        if os.path.isdir(build):
            if not os.path.realpath(build).startswith(packages_dir + '/'):
                sys.exit(f"the build of {name} lies outside .lake/packages")
            print(build, file=dirs)
EOF

# The roots: every source file outside .lake. What they import is found from the build.
mapfile -t roots < <(find . -name '*.lean' -not -path './.lake/*' -not -path './lakefile.lean' |
  sed 's|^\./||; s|\.lean$||; s|/|.|g' | LC_ALL=C sort)
mapfile -t trusted < "$tmp/trusted.txt"

# The search path the build used, the toolchain's library first, built here rather than
# by `lake env`. A panic aborts rather than printing and going on.
export LEAN_PATH="$libdir"
for d in "${trusted[@]}"; do LEAN_PATH="$LEAN_PATH:$PWD/$d"; done
LEAN_PATH="$LEAN_PATH:$PWD/.lake/build/lib/lean"
export LEAN_ABORT_ON_PANIC=1
"$lean" --run "$gate/Gate.lean" "$libdir" "${trusted[@]}" -- "${roots[@]}" -- "$@" >"$tmp/statements.full"

# One line per constant, its name and the digest of its block; the axiom lines as printed.
python3 - "$tmp/statements.full" >"$tmp/statements.txt" <<'EOF'
import hashlib, sys
blocks, axioms, cur = [], [], None
for line in open(sys.argv[1]):
    if line.startswith('axioms of '):
        axioms.append(line)
    elif not line.startswith(' '):
        cur = [line]
        blocks.append(cur)
    else:
        cur.append(line)
for b in blocks:
    print(b[0].split(':', 1)[0], hashlib.sha256(''.join(b).encode()).hexdigest())
sys.stdout.writelines(axioms)
EOF
cat "$tmp/pins.txt" >>"$tmp/statements.txt"

if [ "$update" = 1 ]; then
  cp "$tmp/statements.txt" statements.txt
  echo "wrote statements.txt ($(wc -l <statements.txt) lines)"
elif ! diff -u statements.txt "$tmp/statements.txt"; then
  echo "the statements above changed: if that is intended, rerun with --update and commit statements.txt" >&2
  exit 1
fi
echo "proof gate passed"
