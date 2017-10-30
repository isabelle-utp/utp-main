#ifndef RECORDER_HPP
#define RECORDER_HPP
#include "TCAlgorithm.hpp"

class MapletRecorder {
private:
  TCAlgorithm& algorithm;

public:
  MapletRecorder(TCAlgorithm& algorithm) : algorithm(algorithm) { };
  ~MapletRecorder() = default;
  virtual void initialise();
  virtual void record(index_t i, index_t j);
  virtual void finalise();
};
#endif
