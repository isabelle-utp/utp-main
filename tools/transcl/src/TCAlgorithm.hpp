#ifndef TCALGORITHM_HPP
#define TCALGORITHM_HPP
#include<iostream>
#include<string>
#include<cstddef>

#include "Symtab.hpp"
#include "encode_mode.h"

typedef unsigned int index_t;

class TCAlgorithm {
public:
  virtual string name() = 0;
  virtual void init(size_t size) = 0;
  virtual void clear() = 0;
  virtual size_t vertices() = 0;
  virtual void record(index_t i, index_t j) = 0;
  virtual bool readout(index_t i, index_t j) = 0;
  virtual void execute() = 0;
  size_t maplets();
  void output(Symtab symtab, std::ostream& ss);
  void encode(std::ostream& ss, encode_mode_t mode);
  void cyclic(std::ostream& ss);

private:
  void encode_relation(std::ostream& ss);
  void encode_rangeset(std::ostream& ss);
};
#endif
