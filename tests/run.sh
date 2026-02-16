#!/usr/bin/env bash
# Most common tests
for i in "$@"; do
  case $i in
    --help)
      echo "Available options:"
      echo "    --update   Update files when possible"
      echo "    [STRING]    Only run tests for files containing this string"
      echo "Debugging options"
      echo "    --debug    Print commands as they are run"
      echo "    --dry-run  Print commands without running them"
      exit 0
      ;;
    --update)
      UPDATE=1
      shift
      ;;
    --dry-run)
      # Just print the commands
      ECHO_IF_DRY=echo
      shift
      ;;
    --debug)
      DEBUG=1
      shift
      ;;
    -*)
      echo "Unrecognized option $i"
      exit 1
      ;;
    *)
      NAMED=1
      PARAMS+=" \"$i\""
      shift
      ;;
  esac
done
UI_ARGS=$PARAMS
WHY3_ARGS=$PARAMS
if [ $UPDATE ] ; then
    UI_ARGS+=' --bless'
    WHY3_ARGS_=' --update'
else
    FMT_ARGS+=' --check'
fi
if [ ! $NAMED ] ; then
    WHY3_ARGS+=' --diff-from=origin/master'
fi
if [ $DEBUG ] ; then
    set -x
fi
cd $(dirname "${BASH_SOURCE}")/..
fmt() {
  $ECHO_IF_DRY ./fmt $FMT_ARGS
}
ui() {
    $ECHO_IF_DRY cargo test --test ui -- $UI_ARGS
}
why3() {
    $ECHO_IF_DRY cargo test --test why3 -- $WHY3_ARGS
}
fmt
ui
why3
