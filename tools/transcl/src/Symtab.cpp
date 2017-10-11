#include<iostream>
#include<cstdlib>
#include<string>
#include<vector>
#include<climits>
#include<cassert>
#include"debug.h"

#include"Symtab.hpp"

Symtab::Symtab() { clear(); }

void Symtab::clear() {
  root.reset();
  symbols.clear();
  counter = 1;
}

Symtab::index_t Symtab::operator[](const string& symbol) {
  TrieNode<index_t>* node = &root;
  for(char c : symbol) {
    node = (*node)[c];
  }
  if (!node->hasValue()) {
    /* Assert that an overflow will not occured. */
    assert(counter != 0);
    node->setValue(counter);
    /* Perhaps this is not the most efficient approach! */
    symbols.push_back(symbol);
    counter++;
  }
  /*debug << symbol << " = " << node->getValue() << std::endl;*/
  return node->getValue();
}

string Symtab::operator[](Symtab::index_t symid) {
  if (symid >= 1 && symid < counter) {
    return symbols[symid-1];
  }
  else {
    throw std::invalid_argument(
      "Identifier " + to_string(symid) + " is not in symbol table.");
  }
}

int Symtab::size() {
  return symbols.size();
}

void Symtab::print(ostream& os) {
  for(int i = 1; i <= size(); i++) {
    os << (*this)[i] << " = " << i << endl;
  }
}
