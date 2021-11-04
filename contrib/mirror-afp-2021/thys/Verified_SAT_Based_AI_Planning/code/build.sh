#!/bin/bash

set -e

unzip kissat-master.zip
unzip sml-parse-comb-master.zip

mkdir -p code/generated

isabelle build Verified_SAT_Based_AI_Planning

isabelle export \
  -x 'Verified_SAT_Based_AI_Planning.Solve_SASP:code/SASP_to_DIMACS.ML' \
  -x 'Verified_SAT_Based_AI_Planning.Solve_SASP:code/decode_DIMACS_model.ML' \
  -p 2 -O generated Verified_SAT_Based_AI_Planning

mlton encode_problem.mlb
mlton decode_model.mlb
