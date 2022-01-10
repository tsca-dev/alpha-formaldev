#!/bin/bash

## intended to be used with a one-liner such as
# ./list-interesting-files.sh  | xargs tar czvf certified-contracts.tar.gz

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

(
cd "$DIR"
ls README.md Makefile _CoqProject *.v *.ccg *.tz
)
