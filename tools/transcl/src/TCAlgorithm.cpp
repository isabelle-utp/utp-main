#include<cassert>

#include "TCAlgorithm.hpp"

size_t TCAlgorithm::maplets() {
  size_t count = 0;
  for (index_t i = 0; i < vertices(); i++) {
    for (index_t j = 0; j < vertices(); j++) {
      if (readout(i, j)) count++;
    }
  }
  return count;
}

void TCAlgorithm::output(Symtab symtab, std::ostream& ss) {
  ss << "{";
  bool first = true;
  for (index_t i = 0; i < vertices(); i++) {
    for (index_t j = 0; j < vertices(); j++) {
      if (readout(i, j)) {
        if (first) { first = false; }
        else {
          ss << ", ";
        }
        ss << "(" << symtab[i+1] << ", " << symtab[j+1] << ")";
      }
    }
  }
  ss << "}";
}

void TCAlgorithm::encode(std::ostream& ss, encode_mode_t mode) {
  switch (mode) {
    case relation:
      encode_relation(ss);
      break;

    case range_set:
      encode_rangeset(ss);
      break;

    default:
      assert(false);
  }
}

void TCAlgorithm::encode_relation(std::ostream& ss) {
  ss << vertices() << ";";
  for (index_t i = 0; i < vertices(); i++) {
    for (index_t j = 0; j < vertices(); j++) {
      if (readout(i, j)) {
        ss << i << ";";
        ss << j << ";";
      }
    }
  }
}

void TCAlgorithm::encode_rangeset(std::ostream& ss) {
  ss << vertices() << ";";
  for (index_t j = 0; j < vertices(); j++) {
    bool in_range = false;
    for (index_t i = 0; i < vertices(); i++) {
      in_range |= readout(i, j);
    }
    if (in_range) { ss << j << ";"; }
  }
}

void TCAlgorithm::cyclic(std::ostream& ss) {
  bool is_cyclic = false;
  for (index_t i = 0; i < vertices(); i++) {
    is_cyclic |= readout(i, i);
  }
  ss << (is_cyclic ? "true" : "false");
}
