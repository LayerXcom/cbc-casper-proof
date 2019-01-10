#!/bin/sh

EXECUTABLE=${1:-isabelle}
CMD="build -o quick_and_dirty -j 2 -d . all"

${EXECUTABLE} ${CMD}

