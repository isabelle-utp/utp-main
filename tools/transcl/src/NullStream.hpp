#ifndef nullptrSTREAM_HPP
#define nullptrSTREAM_HPP
#include<ostream>
#include<streambuf>

class NullBuffer : public std::streambuf {
public:
  int overflow(int c) { return c; }
};

class NullStream : public std::ostream {
private:
  NullBuffer null_buffer;

public:
  NullStream() : std::ostream(&null_buffer) { }
};

namespace std {
  extern NullStream nil;
}
#endif
