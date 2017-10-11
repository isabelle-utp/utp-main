#ifndef FLOYDWARSHALL_HPP
#define FLOYDWARSHALL_HPP
#include<string>
#include<cstddef>

#include "TCAlgorithm.hpp"

/* For now, the maximum size of the adjacency matrix is fixed in code. */
#define ADJ_MATRIX_SIZE 1024

typedef bool adj_matrix_t[ADJ_MATRIX_SIZE][ADJ_MATRIX_SIZE];

class FloydWarshall : public TCAlgorithm {
private:
  adj_matrix_t adj_matrix;
  size_t size;

public:
  FloydWarshall() : size(0) { };
  ~FloydWarshall() = default;

  /* Virtual Methods */
  void init(size_t size);
  void clear();
  void execute();

  /* Inline Methods */
  inline string name() { return "floyd-warshall"; }
  inline size_t vertices() { return size; }
  inline void record(index_t i, index_t j) { adj_matrix[i][j] = true; }
  inline bool readout(index_t i, index_t j) { return adj_matrix[i][j]; }
};
#endif
