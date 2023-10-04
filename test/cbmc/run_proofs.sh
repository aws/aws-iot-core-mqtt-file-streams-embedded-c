#!/bin/sh

coreJSONDir="coreJSON"

UNWIND_COUNT=${UNWIND_COUNT:-10}

#If coreJSON not found, clone it
if [ ! -d "$coreJSONDir" ]; then
    git clone https://github.com/FreeRTOS/coreJSON.git --depth 1 --branch v3.2.0
fi

cd "$(dirname -- "$0")/../../" || exit 1

exec cbmc source/MQTTFileDownloader.c source/MQTTFileDownloader_cbor.c \
     source/MQTTFileDownloader_base64.c test/cbmc/coreJSON/source/core_json.c \
     test/cbmc/proofs.c -Isource/include -Itest/cbmc/coreJSON/source/include \
     -Itest/unit-test/dependencies \
     --unwindset strlen.0:36 \
     --bounds-check --pointer-check --memory-cleanup-check --div-by-zero-check \
     --signed-overflow-check --unsigned-overflow-check --pointer-overflow-check \
     --conversion-check --undefined-shift-check --enum-range-check \
     --pointer-primitive-check --drop-unused-functions --nondet-static \
     --unwinding-assertions --c99 --trace "$@" --unwind "$UNWIND_COUNT" \
     -DUNWIND_COUNT="$UNWIND_COUNT" >&1 | tee test/cbmc/output/cbmcOutput.txt