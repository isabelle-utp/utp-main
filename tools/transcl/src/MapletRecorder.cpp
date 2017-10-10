#include<iostream>

#include "MapletRecorder.hpp"
#include "main.h"
#include "debug.h"

void MapletRecorder::initialise() {
  algorithm.clear();
  /* When producing output for Isabelle/UTP. */
  if (args.encode_output) {
    outp << algorithm.vertices() << ";";
  }
}

void MapletRecorder::record(index_t i, index_t j) {
  /*debug << "Maplet: (" << id1 << ", " << id2 << ")" << endl;*/
  algorithm.record(i, j);
  /* When producing output for Isabelle/UTP. */
  if (args.encode_output) {
    outp << i << ";";
    outp << j << ";";
  }
}

void MapletRecorder::finalise() {
  /* When producing output for Isabelle/UTP. */
  if (args.encode_output) {
    outp << endl;
  }
}
