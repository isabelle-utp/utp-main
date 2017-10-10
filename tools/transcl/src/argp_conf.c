#include<cstring>
#include"errno.h"
#include"debug.h"

#include "argp_conf.h"

/* Global args_t structure. */
struct args_t args;

/* Argp Setup */
const char *argp_program_version = "transcl 1.0";

const char *argp_program_bug_address = "<frank.zeyda@york.ac.uk>";

const char algorithm_option_doc[] =
  "Select the algorithm to be used. Possible values are floyd-warshall and boost, the latter using graph algorithms of the C++ Boost Library. The default value is floyd-warshall.";

const char encode_option_doc[] =
  "Encode output for reconstruction in Isabelle/HOL. Possible values for TYPE are \"rel\" and \"set\", where the latter merely outputs the range set of the closure but not the entire relation.";

const char acyclic_option_doc[] =
  "Only determine whether the relation is acyclic. This outputs either \"true\" or \"false\".";

const char output_file_option_doc[] =
  "Output to FILE instead of the standard output.";

struct argp_option options[] = {
  {"algorithm",   'a', "NAME",  0, algorithm_option_doc },
  {"encode",      'e', "TYPE",  OPTION_ARG_OPTIONAL, encode_option_doc },
  {"cyclic",      'c', nullptr, 0, acyclic_option_doc },
  {"output-file", 'o', "FILE",  0, output_file_option_doc },
  { 0 }
};

error_t parse_opt (int key, char *arg, struct argp_state *state) {
  struct args_t *args = (struct args_t *) state->input;
  switch (key) {
    case 'a':
      try {
        args->algorithm = Algorithms.get_by_name(arg);
      }
      catch (invalid_argument& e) {
        cerr << "transcl: invalid algorithm name " << "\"" << arg << "\"";
        cerr << endl;
        argp_state_help(state, stdout, ARGP_HELP_SEE);
        return EINVAL;
      }
      break;

    case 'e':
      args->encode_output = true;
      if (arg != nullptr) {
        if (strcmp(arg, "rel") == 0) {
          args->encode_mode = relation;
        }
        else
        if (strcmp(arg, "set") == 0) {
          args->encode_mode = range_set;
        }
        else {
          cerr << "transcl: invalid encoding type " << "\"" << arg << "\"";
          cerr << endl;
          argp_state_help(state, stdout, ARGP_HELP_SEE);
          return EINVAL;
        }
      }
      break;

    case 'c':
      args->check_cyclic = true;
      break;

    case 'o':
      args->output_file = arg;
      break;

    case ARGP_KEY_INIT:
      debug << "ARGP_KEY_INIT" << endl;
      break;

    case ARGP_KEY_ARG:
      debug << "ARGP_KEY_ARG" << endl;
      if (state->arg_num == 0) {
        args->input_file = arg;
      }
      else {
        return ARGP_ERR_UNKNOWN;
      }
      break;

    case ARGP_KEY_NO_ARGS:
      debug << "ARGP_KEY_NO_ARGS" << endl;
      break;

    case ARGP_KEY_END:
      debug << "ARGP_KEY_END" << endl;
      if (args->encode_output && args->check_cyclic) {
        cerr << "options --encode and --cyclic are mutually exclusive";
        cerr << endl;
        argp_state_help(state, stdout, ARGP_HELP_SEE);
        return EINVAL;
      }
      break;

    case ARGP_KEY_SUCCESS:
      debug << "ARGP_KEY_SUCCESS" << endl;
      break;

    case ARGP_KEY_ERROR:
      debug << "ARGP_KEY_ERROR" << endl;
      break;

    case ARGP_KEY_FINI:
      debug << "ARGP_KEY_FINI" << endl;
      break;

    default:
      return ARGP_ERR_UNKNOWN;
  }
  return 0;
}

const char args_doc[] = "[INPUT_FILE]";

const char help_doc[] = "\n  The transcl command calculates and outputs the \
transitive closure of a relation, supporting various algorithms. If no \
INPUT_FILE is specified, the relation is read from the standard input. By \
default, the result is written to the standard output, unless the option -o \
is specified.\n\nOptions:";

struct argp argp = { options, parse_opt, args_doc, help_doc };

void setDefaults(args_t& args) {
  args.algorithm = floyd_warshall;
  args.encode_output = false;
  args.encode_mode = relation;
  args.check_cyclic = false;
  args.input_file = nullptr;
  args.output_file = nullptr;
}
