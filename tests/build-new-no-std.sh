#!/usr/bin/env bash
# Test that we can build a minimal no-std project
set -x
TLC=$(rustup show active-toolchain | cut -d " " -f1)
rustup component add --toolchain $TLC rustfmt
rustup component add --toolchain $TLC rust-src
rustup target add thumbv7em-none-eabi
cd ..
DIR=creusot-test-please-ignore
rm -rf $DIR
cargo creusot new $DIR --no-std --creusot-std ../creusot/creusot-std
cd $DIR
echo $TLC > rust-toolchain
cargo fmt --check
cargo build
cargo build --target thumbv7em-none-eabi -Zbuild-std=core,alloc
cargo creusot prove
cargo creusot prove -- --target thumbv7em-none-eabi -Zbuild-std=core,alloc
