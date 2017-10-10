#ifndef SYMTAB_HPP
#define SYMTAB_HPP
#include<iostream>
#include<string>
#include<vector>

#include"TrieNode.cpp"

using namespace std;

template class TrieNode<int>;

class Symtab {
public:
  /* Indices are represented by unsigned integers. */
  typedef unsigned int index_t;

protected:
  /* Root of the trie encoding for the symbol table. */
  TrieNode<index_t> root;
  /* Array used to store symbols by their index. */
  vector<string> symbols;
  /* Counter for generating the next index. */
  index_t counter;

public:
  Symtab();
  ~Symtab() = default;

  /* Remove all entries from the symbol table. */
  void clear();

  /* Obtain the identifier of a symobl; create if not present. */
  index_t operator[](const string& symbol);

  /* Obtain the symbol for a given identifier. */
  string operator[](index_t symid);

  /* Return the number of symbols in the table. */
  int size();

  /* Print the content of the symbol table. */
  void print(ostream& os);
};
#endif
