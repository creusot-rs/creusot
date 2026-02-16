#!/usr/bin/env bash
set -ex
export RUSTFLAGS="-D warnings"
cd ..
DIR=creusot-test-please-ignore
rm -rf $DIR
cargo creusot new $DIR --main --creusot-std ../creusot/creusot-std
cd $DIR
cargo fmt --check
cargo build
cargo creusot
cargo creusot prove
