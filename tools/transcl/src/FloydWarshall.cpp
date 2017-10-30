#include<stdexcept>

#include "FloydWarshall.hpp"

void FloydWarshall::init(size_t size) {
  if (size > ADJ_MATRIX_SIZE) {
    throw std::logic_error(
      "Number of vertices exceeds fixed adjecency matrix size.");
  }
  this->size = size;
}

void FloydWarshall::clear() {
  for (index_t i = 0; i < size; i++) {
    for (index_t j = 0; j < size; j++) {
      adj_matrix[i][j] = false;
    }
  }
}

void FloydWarshall::execute() {
  for (index_t k = 0; k < size; k++) {
    for (index_t i = 0; i < size; i++) {
      for (index_t j = 0; j < size; j++) {
        adj_matrix[i][j] |= adj_matrix[i][k] & adj_matrix[k][j];
      }
    }
  }
}
