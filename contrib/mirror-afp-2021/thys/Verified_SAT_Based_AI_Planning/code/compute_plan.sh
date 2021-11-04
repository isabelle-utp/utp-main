#!/bin/bash

function help_message(){
  echo "Usage ./compute_plan.sh horizon problem SAT_solver_executable"
  echo "Note: horizon is a number\n problem is a SAS+ problem in FastDownward's format\n SAT_solver_executable is a path to an executable that accepts DIMACS SAT formulae in its stdin, and it has to output a model as a sequence of integers with only spaces between them"
  exit
}

if [ -z "$1" ]; then
  help_message
fi

if [ -z "$2" ]; then
  help_message
fi

if [ -z "$3" ]; then
  help_message
fi

horizon=$1
problem=$2
SAT_Solver=$3

cat $problem | sed -n '/begin_SG/q;p' > /tmp/op_prob

./encode_problem /tmp/op_prob $horizon | sed 's/~/-/g' | $SAT_Solver > /tmp/op_model

./decode_model /tmp/op_prob <(grep "v " /tmp/op_model | sed 's/v //g' | sed 's/ 0//g') $horizon
