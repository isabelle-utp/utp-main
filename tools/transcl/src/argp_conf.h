#ifndef ARGP_CONF_H
#define ARGP_CONF_H
#include "argp.h"
#include "encode_mode.h"

#include "Algorithms.hpp"

struct args_t {
  algorithm_t algorithm;
  bool encode_output;
  encode_mode_t encode_mode;
  bool check_cyclic;
  char *input_file;
  char *output_file;
};

extern struct args_t args;

extern struct argp argp;

/* Function Prototypes */
void setDefaults(args_t& args);
#endif
