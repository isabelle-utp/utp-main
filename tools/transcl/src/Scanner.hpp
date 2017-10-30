#ifndef SCANNER_HPP
#define SCANNER_HPP
#include<fstream>
#include<cstddef>
#include<cassert>

#include "Symtab.hpp"
#include "MapletRecorder.hpp"
#include "ScanException.hpp"

#define MAX_TOKEN_SIZE 65536

/* Used to calculate line positions for error messages. */
#define TAB_SIZE 8

using namespace std;

/* Note that scan_index points to the next character to be read. Moreover,
 * scan_index points one character ahead. So, after, for instance, reading
 * the first two characters scan_index would be 3. For efficienct and to
 * minimise elementary array accesses, we record both the current and next
 * character in local variables, giving us a look-ahead of one character. */
class Scanner {
protected:
  /* File content in memory */
  char *file_content = nullptr;
  streamsize file_size = 0;

  /* Scanning indices */
  int scan_index;
  int line, pos;
  /* For efficiency reasons */
  char curr_char;
  char next_char;
  bool curr_valid;

  /* Token management */
  char token[MAX_TOKEN_SIZE + 1];
  int token_index = 0;
  size_t token_length = 0;

public:
  /* Constructors and Destructor */
  Scanner();
  Scanner(string filename) throw (ios_base::failure);
  ~Scanner();

  /* Inline Methods */
  inline bool more() {
    /* Note that scan_index points one character ahead. */
    return scan_index <= file_size;
  }

  inline bool eof() {
    /* Note that scan_index points one character ahead. */
    return scan_index == file_size + 1;
  }

  inline char valid() {
    return curr_valid;
  }

  inline char current() {
    assert(valid());
    return curr_char;
  }

  inline char next() {
    assert(more());
    return next_char;
  }

  /* Public Methods */
  void fromString(const string& text);
  void readFile(string filename) throw (ios_base::failure);
  void initScan();
  bool skipWS();
  bool skipSymbol(char c);
  bool scanSymbol(char c);
  bool scanUntil(char until);
  bool scanString();
  bool scanHOLString();
  bool scanTerm(char until);
  void scanRelation(Symtab& symtab, MapletRecorder *mrec = nullptr);

protected:
  /* Internal Methods */
  void clearToken();
  void processLinePos();
  char advance();
  void consume();
  void freeMemory();
};
#endif
