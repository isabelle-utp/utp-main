#ifndef SCANEXCEPTION_HPP
#define SCANEXCEPTION_HPP
#include<string>
#include<exception>
#include<sstream>

using namespace std;

class ScanException : public exception, public stringstream {
protected:
  const int line, pos;

public:
  ScanException(int line, int pos);
  ScanException(string msg, int line, int pos);
  ScanException(const ScanException&);
  ~ScanException() = default;

  virtual const char *what() const noexcept;

  void displayError();
};
#endif
