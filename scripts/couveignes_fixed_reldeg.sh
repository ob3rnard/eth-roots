#!/bin/bash

# Code in support of arXiv:xxxx.xxxxx [pp.sss]
# Copyright 2023, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)


# Script folder
EXE_DIR=$(dirname $(readlink -f $0));

# Data / Logs folder
DATA_ROOT=$(dirname ${EXE_DIR});
DATA_DIR="${DATA_ROOT}/data"; 
LOGS_DIR="${DATA_ROOT}/logs";

# Just check that parent folders are indeed where they should be
[[ ! -d ${DATA_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Data directory ${DATA_DIR} does not exist.";
    exit 1;
};

[[ ! -d ${LOGS_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Logs directory ${LOGS_DIR} does not exist.";
    exit 1;
};

NUMBER_TESTS=10

# compute timings for rel. couveignes vs nfroots : p fixed = rel. degree [K:k]
for p in "$@"; do
    exp="$p"
    
    sage ${EXE_DIR}/couveignes_fixed_reldeg.sage ${exp} ${NUMBER_TESTS} pari 1>${LOGS_DIR}/couv_fixed_reldeg_${exp}_pari 2>&1 &

    sage ${EXE_DIR}/couveignes_fixed_reldeg.sage ${exp} ${NUMBER_TESTS} padic 1>${LOGS_DIR}/couv_fixed_reldeg_${exp}_padic 2>&1 &

    sage ${EXE_DIR}/couveignes_fixed_reldeg_nfroots.sage ${exp} ${NUMBER_TESTS}  1>${LOGS_DIR}/couv_fixed_reldeg_${exp}_nfroots 2>&1 &
    
done;

exit 0;
