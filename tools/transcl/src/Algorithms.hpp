#ifndef ALGORITHMS_H
#define ALGORITHMS_H
#include<iostream>
#include<map>

#include "TCAlgorithm.hpp"

typedef enum { floyd_warshall, boost_algorithm } algorithm_t;

class Algorithms {
private:
  map<string, algorithm_t> algo_by_name;

public:
  Algorithms();
  ~Algorithms() = default;

  algorithm_t get_by_name(string);

  TCAlgorithm* create(algorithm_t);
};

extern class Algorithms Algorithms;
#endif
