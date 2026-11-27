#!/bin/bash
# On a fresh Ubuntu 22.04 machine (an EC2 instance, a RunPod CPU pod), as root: the checkers at the commits CI pins,
# the repo at a given ref, and Lean's Init export, in /workspace. usage: setup.sh <git ref>
# Then scripts/cloud/run.sh proves and checks a range of theorem-all's chunks (docs/milestone3.md, "Running it").
set -euxo pipefail
REF=${1:?ref}
export HOME=${HOME:-/root}
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq && apt-get install -y -qq git curl ca-certificates build-essential python3 openjdk-11-jdk-headless zstd >/dev/null
W=/workspace; mkdir -p $W/mm/setmm $W/mm/mmj2/macros; cd $W
curl -fsSL https://dot.net/v1/dotnet-install.sh -o di.sh && bash di.sh --channel 10.0 --install-dir $W/dotnet >/dev/null
export PATH=$W/dotnet:$PATH DOTNET_ROOT=$W/dotnet DOTNET_CLI_TELEMETRY_OPTOUT=1
curl -fsSL -o mm/setmm/set.mm https://raw.githubusercontent.com/metamath/set.mm/6315535f37e5e58d14ece8c34ddb204926446264/set.mm
git clone -q https://github.com/metamath/metamath-exe mm/metamath-exe && git -C mm/metamath-exe checkout -q 580b4bd5ae6f2a0d746398b0033cddccba1b418b
cc -O2 -w -o mm/metamath mm/metamath-exe/src/*.c
git clone -q https://github.com/david-a-wheeler/mmverify.py mm/mmverify && git -C mm/mmverify checkout -q 63a2aa3815cd5bf67892dbfc7f2048cbb177524c
raw=https://raw.githubusercontent.com/digama0/mmj2/c8dd05548139c7003220caedde65a7abe44a00bf/mmj2jar
curl -fsSL -o mm/mmj2/mmj2.jar $raw/mmj2.jar; for m in definitionCheck init; do curl -fsSL -o mm/mmj2/macros/$m.js $raw/macros/$m.js; done
git clone -q https://github.com/keithadler/tenet-zfc repo && git -C repo fetch -q origin "$REF" && git -C repo checkout -q FETCH_HEAD
(cd repo && dotnet build src/TenetZfc.Cli -c Release -f net10.0 2>&1 | tail -2)
# Lean's Init, as the workflow exports it.
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none >/dev/null
export PATH=$HOME/.elan/bin:$PATH
git clone -q https://github.com/keithadler/leanout && git -C leanout checkout -q 0562d84c5bad6e94f6c330754d61e51324fc905e
(cd leanout && lake build leanout 2>&1 | tail -1 && .lake/build/bin/leanout Init -o $W/init.ndjson)
cat > $W/env.sh <<EOT
export PATH=$W/dotnet:\$HOME/.elan/bin:\$PATH DOTNET_ROOT=$W/dotnet DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_GCConserveMemory=7
export TENET_ZFC_SETMM=$W/mm/setmm TENET_ZFC_METAMATH=$W/mm/metamath TENET_ZFC_MMVERIFY=$W/mm/mmverify/mmverify.py TENET_ZFC_JAVA=java TENET_ZFC_MMJ2=$W/mm/mmj2
EOT
ls -l $W/init.ndjson; echo SETUP-DONE
