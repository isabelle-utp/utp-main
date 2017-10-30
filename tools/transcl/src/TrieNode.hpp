#ifndef TRIENODE_HPP
#define TRIENODE_HPP
#include<map>

template <class T>
class TrieNode {
/*friend class Symtab;*/

private:
  /* Does this node have a value? */
  bool has_value;
  /* Value of the node, if present. */
  T value;
  /* Child nodes of the trie object. */
  std::map<char, TrieNode> children;

public:
  TrieNode();
  ~TrieNode() = default;

  /* Reset the value and children of this node. */
  void reset();

  /* Does this node have a value? */
  bool hasValue();

  /* Get the value of this node. */
  T getValue();

  /* Set the value of this node. */
  void setValue(T new_value);

  /* Obtain child by index, create if it does not exists. */
  TrieNode<T>* operator[](char c);
};
#endif
