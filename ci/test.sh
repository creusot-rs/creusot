#!/bin/sh

set -x

for f in gold-tests/*.rs
do
  filename="$(basename $f)"
  filename="${filename%.*}"
  out_file=$(mktemp -d)/modules.mlcfg
  cargo run -- -L $(pwd)/target/debug/ $f > $out_file
done
