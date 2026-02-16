#!/usr/bin/env bash
for i in "$@"; do
  case $i in
    --help)
      echo "Commands (default: fmt ui why3):"
      echo "    fmt          Fix formatting of .rs files"
      echo "    ui           Test Creusot compiler output"
      echo "    why3         Test Why3 proofs"
      echo "    build-new    Build new project"
      echo "    build-no-std Build new project, no-std"
      echo "Options:"
      echo "    --update     Update files (tests: ui, why3)"
      echo "    --fmt-check  Only check formatting of .rs files"
      echo "    --why3-all   Run why3 test on all .coma files"
      echo "                 (default is .coma files with changes from origin/master)"
      echo "    [STRING]     Only run tests for files containing this string (tests: ui, why3)"
      echo "    --debug      Print commands as they are run"
      exit 0
      ;;
    all)
      TEST_ALL=1
      shift
      ;;
    fmt)
      TEST_FMT=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    ui)
      TEST_UI=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    why3)
      TEST_WHY3=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    erasure-check)
      TEST_ERASURE_CHECK=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    build-new)
      TEST_BUILD_NEW=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    build-no-std)
      TEST_BUILD_NO_STD=1
      NO_TEST_DEFAULT=1
      shift
      ;;
    --fmt-check)
      FMT_CHECK=1
      shift
      ;;
    --update)
      UPDATE=1
      shift
      ;;
    --debug)
      DEBUG=1
      shift
      ;;
    --why3-all)
      WHY3_DIFF_FROM=0
      shift
      ;;
    -*)
      echo "Unrecognized option $i"
      exit 1
      ;;
    *)
      WHY3_DIFF_FROM=0
      PARAMS+=("$i")
      shift
      ;;
  esac
done
if [ ! "$NO_TEST_DEFAULT" ] ; then
  TEST_FMT=1
  TEST_UI=1
  TEST_WHY3=1
fi
UI_ARGS=("${PARAMS[@]}")
WHY3_ARGS=("${PARAMS[@]}")
if [ "$UPDATE" ] ; then
  UI_ARGS+=(--bless)
  WHY3_ARGS+=(--update)
fi
if [ "$FMT_CHECK" ] ; then
  FMT_ARGS+=(--check)
fi
if [ "$WHY3_DIFF_FROM" != 0 ] ; then
  WHY3_ARGS+=("--diff-from=origin/master")
fi
if [ "$DEBUG" ] ; then
    set -x
fi
BOLD=$'\e[1m'
GREEN=$'\e[0;32m'
YELLOW=$'\e[0;33m'
STYLE_OFF=$'\e[0m'
cd "$(dirname "${BASH_SOURCE[0]}")"
if [ "$TEST_FMT" ] || [ "$TEST_ALL" ] ; then
  if [ "$FMT_CHECK" ] ; then
    echo ">>> ${BOLD}Check fmt${YELLOW}"
  else
    echo ">>> ${BOLD}Fix fmt${GREEN}"
  fi
  ./fmt -l "${FMT_ARGS[@]}"
  echo -n "$STYLE_OFF"
fi
set -e
if [ "$TEST_UI" ] || [ "$TEST_ALL" ] ; then
  echo ">>> ${BOLD}Test creusot compiler${STYLE_OFF}"
  cargo test --test ui -- "${UI_ARGS[@]}"
fi
if [ "$TEST_WHY3" ] || [ "$TEST_ALL" ] ; then
  echo ">>> ${BOLD}Test Why3 proofs${STYLE_OFF}"
  cargo test --test why3 -- "${WHY3_ARGS[@]}"
fi
if [ "$TEST_ERASURE_CHECK" ] || [ "$TEST_ALL" ] ; then
  echo ">>> ${BOLD}Test erasure check${STYLE_OFF}"
  rustup component add rust-src
  cargo test --test ui -- --erasure-check
fi
if [ "$TEST_BUILD_NEW" ] || [ "$TEST_ALL" ] ; then
  echo ">>> ${BOLD}Test build-new${STYLE_OFF}"
  export RUSTFLAGS="-D warnings"
  pushd ..
  DIR=creusot-test-please-ignore
  rm -rf $DIR
  cargo creusot new $DIR --main --creusot-std ../creusot/creusot-std
  cd $DIR
  cargo fmt --check
  cargo build
  cargo creusot
  cargo creusot prove
  popd
fi
if [ "$TEST_BUILD_NO_STD" ] || [ "$TEST_ALL" ] ; then
  echo ">>> ${BOLD}Test build-no-std${STYLE_OFF}"
  export RUSTFLAGS="-D warnings"
  TLC=$(rustup show active-toolchain | cut -d " " -f1)
  rustup component add --toolchain "$TLC" rustfmt
  rustup component add --toolchain "$TLC" rust-src
  rustup target add thumbv7em-none-eabi
  DIR=creusot-test-please-ignore
  pushd ..
  rm -rf $DIR
  cargo creusot new $DIR --no-std --creusot-std ../creusot/creusot-std
  cd $DIR
  echo "$TLC" > rust-toolchain
  cargo fmt --check
  cargo build
  cargo build --target thumbv7em-none-eabi -Zbuild-std=core,alloc
  cargo creusot prove
  cargo creusot prove -- --target thumbv7em-none-eabi -Zbuild-std=core,alloc
  popd
fi
