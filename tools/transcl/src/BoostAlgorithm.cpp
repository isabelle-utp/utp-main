#include "BoostAlgorithm.hpp"

#include "boost/graph/transitive_closure.hpp"

using namespace boost;

BoostAlgorithm::BoostAlgorithm() : size(0), graph(nullptr) { }

BoostAlgorithm::~BoostAlgorithm() {
  if (graph != nullptr) delete graph;
}

void BoostAlgorithm::init(size_t size) {
  if (graph != nullptr) delete graph;
  graph = new graph_t(size);
  this->size = size;
}

void BoostAlgorithm::clear() {
  graph->clear();
}

void BoostAlgorithm::execute() {
  /* Supplying size here, even if correct, does not work...! */
  graph_t *result = new graph_t(/*size*/);
  transitive_closure(*graph, *result);
  if (graph != nullptr) delete graph;
  graph = result;
}
