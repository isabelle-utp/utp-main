#include<iostream>
#include<fstream>
#include<sstream>
#include<string>
#include<iterator>
#include<stdexcept>
#include<cstdlib>
#include<cstring>
#include<cassert>
#include"debug.h"

#include "main.h"

#include "Symtab.hpp"
#include "Scanner.hpp"
#include "Algorithms.hpp"

#define DEBUG false

using namespace std;

std::ofstream* file = nullptr;

void openOutputFile() {
  if (args.output_file != nullptr) {
    try {
      file = new ofstream();
      file->exceptions(ifstream::failbit | ifstream::badbit);
      file->open(args.output_file);
    }
    catch (ios_base::failure) {
      cerr << "Error writing file \"" << args.output_file << "\".";
      debug << endl;
      exit(EXIT_FAILURE);
    }
  }
}

void closeOutputFile() {
  if (args.output_file != nullptr) {
    try {
      file->close();
    }
    catch (ios_base::failure) {
      cerr << "Error writing file \"" << args.output_file << "\".";
      debug << endl;
      exit(EXIT_FAILURE);
    }
  }
}

error_t parse_args(int argc, char *argv[]) {
  /* Set default options */
  setDefaults(args);
  /* Invoke argp parser */
  bool debug_flag = debug_enabled;
  disable_debug();
  /* Could this return an error? Do we need to check? */
  error_t result = argp_parse(&argp, argc, argv, 0, 0, &args);
  if (debug_flag) enable_debug();
  return result;
}

void readInput(Scanner& scanner) {
  if (args.input_file == nullptr) {
    debug << "Terminate with [RETURN] followed by [CTRL+D]." << endl;
    debug << "> ";
    /* Read relation from the standard input stream. */
    cin >> std::noskipws;
    std::istream_iterator<char> iter(std::cin);
    std::istream_iterator<char> end;
    /* Can this fail and if so, in what way? */
    scanner.fromString(string(iter, end));
  }
  else {
    try {
      scanner.readFile(args.input_file);
    }
    catch (ios_base::failure) {
      cerr << "Error reading file \"" << args.input_file << "\"." << endl;
      exit(EXIT_FAILURE);
    }
  }
}

void writeOutput(Symtab& symtab, TCAlgorithm& algorithm) {
  debug << "[Transitive Closure]" << endl;
  try {
    if (args.encode_output) {
      encode_mode_t mode = args.encode_mode;
      algorithm.encode(outp, mode);
      if (args.output_file != NULL) {
        algorithm.encode(debug, mode);
      }
    }
    else if (args.check_cyclic) {
      algorithm.output(symtab, debug);
      debug << endl;
      algorithm.cyclic(outp);
    }
    else {
      algorithm.output(symtab, outp);
      if (args.output_file != NULL) {
        algorithm.output(symtab, debug);
      }
    }
    /*debug << endl;*/
  }
  catch (ios_base::failure) {
    cerr << "Error writing file \"" << args.output_file << "\".";
    debug << endl;
    exit(EXIT_FAILURE);
  }
}

void parseRelation(Symtab& symtab, Scanner& scanner, TCAlgorithm& algorithm) {
  try {
    debug << "Scanning relation (pass 1)..." << endl;
    scanner.scanRelation(symtab);
    debug << "[Symbol table]" << endl;
    symtab.print(debug);
    algorithm.init(symtab.size());
    debug << "Scanning relation (pass 2)..." << endl;
    MapletRecorder mrec(algorithm);
    scanner.scanRelation(symtab, &mrec);
    debug << "[Initial Relation]" << endl;
    algorithm.output(symtab, debug);
    debug << endl;
  }
  catch (ScanException& e) {
    e.displayError(); debug << endl;
    exit(EXIT_FAILURE);
  }
}

void execute(TCAlgorithm& algorithm) {
  debug << "Executing " << algorithm.name() << " algorithm..." << endl;
  algorithm.execute();
}

int main(int argc, char* argv[]) {
  if (DEBUG) enable_debug();
  Symtab symtab;
  TCAlgorithm *algorithm;
  /* Parse options */
  error_t result = parse_args(argc, argv);
  if (result != 0) { return EXIT_FAILURE; }
  openOutputFile();
  /* Read input */
  Scanner scanner;
  readInput(scanner);
  /* Parse Relation */
  algorithm = Algorithms.create(args.algorithm);
  parseRelation(symtab, scanner, *algorithm);
  /* Execute algorithm */
  execute(*algorithm);
  /* Write result */
  writeOutput(symtab, *algorithm);
  /* Report success and clean up */
  cerr << "[OK]"; debug << endl;
  closeOutputFile();
  delete algorithm;
  return EXIT_SUCCESS;
}
