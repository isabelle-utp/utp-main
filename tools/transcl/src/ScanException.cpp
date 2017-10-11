#include<iostream>

#include "ScanException.hpp"

using namespace std;

ScanException::ScanException(int line, int pos) : line(line), pos(pos) { }

ScanException::ScanException(string msg, int line, int pos)
  : ScanException(line, pos) {
  str(msg);
}

ScanException::ScanException(const ScanException& obj)
  : ScanException(obj.line, obj.pos) {
  str(obj.str());
}

const char *ScanException::what() const noexcept {
  /* The below does not work since str() creates a temporary string object
   * that does not appear to outlive the method invocation. */
  /*return str().c_str();*/

  /* This works but how are we going to dealloclate the string object now?
   * Due to the method being consts, neither can we retain a handle to it! */
  return (new string(str()))->c_str();
}

void ScanException::displayError() {
  cerr << "Error in line " << line << ", pos " << pos << ": " << str();
}
