#ifndef TRIENODE_CPP
#define TRIENODE_CPP
#include<cassert>

#include"TrieNode.hpp"

template <class T>
TrieNode<T>::TrieNode() {
  reset();
}

template <class T>
void TrieNode<T>::reset() {
  has_value = false;
  children.clear();
}

template <class T>
bool TrieNode<T>::hasValue() {
  return has_value;
}

template <class T>
T TrieNode<T>::getValue() {
  assert(hasValue());
  return value;
}

template <class T>
void TrieNode<T>::setValue(T new_value) {
  value = new_value;
  has_value = true;
}

template <class T>
TrieNode<T>* TrieNode<T>::operator[](char c) {
  return &children[c];
}
#endif
