#ifndef BOOSTALGORITHM_HPP
#define BOOSTALGORITHM_HPP
#include<string>
#include<cstddef>

#include "TCAlgorithm.hpp"

#include "boost/graph/adjacency_list.hpp"

using namespace boost;

/* I am not entirely sure about the first two types below. Efficiency? */
typedef adjacency_list<vecS, vecS, directedS, index_t> graph_t;

class BoostAlgorithm : public TCAlgorithm {
private:
  graph_t *graph;
  size_t size;

public:
  BoostAlgorithm();
  ~BoostAlgorithm();

  /* Virtual Methods */
  void init(size_t size);
  void clear();
  void execute();

  /* Inline Methods */
  inline string name() { return "boost"; }
  inline size_t vertices() { return size; }
  inline void record(index_t i, index_t j) {
    add_edge(i, j, *graph);
  }
  inline bool readout(index_t i, index_t j) {
    return edge(i, j, *graph).second;
  }
};
#endif
