#include<stdexcept>
#include<cassert>

#include "Algorithms.hpp"
#include "FloydWarshall.hpp"
#include "BoostAlgorithm.hpp"

class Algorithms Algorithms;

Algorithms::Algorithms() {
  algo_by_name["floyd-warshall"] = floyd_warshall;
  algo_by_name["boost"] = boost_algorithm;
}

algorithm_t Algorithms::get_by_name(string name) {
  try {
    return algo_by_name.at(name);
  }
  catch (std::out_of_range& e) {
    throw std::invalid_argument("unknown algorithm");
  }
}

TCAlgorithm* Algorithms::create(algorithm_t algorithm) {
  switch(algorithm) {
    case floyd_warshall:
      return new FloydWarshall();

    case boost_algorithm:
      return new BoostAlgorithm();

    default:
      assert(false);
  }
}
