#include<iostream>
#include<sstream>
#include<string>
#include<cstring>
#include"debug.h"

#include "Scanner.hpp"

using namespace std;

Scanner::Scanner() { }

Scanner::Scanner(string filename) throw (ios_base::failure) {
  readFile(filename);
  initScan();
}

Scanner::~Scanner() {
  freeMemory();
}

void Scanner::fromString(const string& text) {
  freeMemory();
  file_size = text.size();
  file_content = new char[text.size() + 1];
  strcpy(file_content, text.c_str());
  file_content[file_size] = '\0';
}

void Scanner::readFile(string filename) throw (ios_base::failure) {
  freeMemory();
  ifstream file;
  file.exceptions(ifstream::failbit | ifstream::badbit);
  file.open(filename);
  file.seekg(0, ios::end);
  file_size = file.tellg();
  /* For homogeneity (next_char), we add an additional entry. */
  file_content = new char[file_size + 1];
  file_content[file_size] = '\0';
  file.seekg(0, ios::beg);
  file.read(file_content, file_size);
  file.close();
  initScan();
}

void Scanner::freeMemory() {
  if (file_content != nullptr) {
    delete[] file_content;
    file_content = nullptr;
    file_size = 0;
  }
}

void Scanner::initScan() {
  assert(file_content != nullptr);
  scan_index = 0;
  line = pos = 0;
  curr_valid = false;
  /* This is safe since we increase the size of file_content by one. */
  next_char = file_content[scan_index++];
  clearToken();
}

void Scanner::clearToken() {
  token[0] = '\0';
  token_index = 0;
  token_length = 0;
}

void Scanner::processLinePos() {
  if (valid()) {
    switch (current()) {
      case '\n':
        line++;

      case '\r':
        pos = 0;
        break;

      case '\t':
        pos += TAB_SIZE - (pos % TAB_SIZE);
        break;

      case '\b':
        if (pos > 0) { pos--; }
        break;

      /* Do we support the following two as well? */
      /*case '\f':*/
      /*case '\v':*/

      default:
        pos++;
    }
  }
}

char Scanner::advance() {
  processLinePos();
  if (!more()) {
    throw ScanException("Unexpected end-of-input", line, pos);
  }
  else {
    curr_char = next_char;
    next_char = file_content[scan_index++];
    curr_valid = true;
  }
  return curr_char;
}

void Scanner::consume() {
  assert(valid());
  if (token_index < MAX_TOKEN_SIZE) {
    token[token_index++] = current();
  }
  else {
    ScanException exn(line, pos);
    exn << "Maximum token lentgh of " << MAX_TOKEN_SIZE << " exceeded.";
    throw exn;
  }
}

bool Scanner::skipWS() {
  while (more()) {
    if (current() == ' ' ||
        current() == '\t' ||
        current() == '\n' ||
        current() == '\r' ||
        current() == '\f') {
      advance();
    }
    else { break; }
  }
  return more();
}

bool Scanner::skipSymbol(char c) {
  if (eof()) {
    ScanException exn(line, pos);
    exn << "End-of-input when expecting \"" << c << "\".";
    throw exn;
  }
  if (current() == c) {
    advance();
  }
  else {
    ScanException exn(line, pos);
    exn << "Expected \"" << c << "\" but \"" << current() << "\" was found.";
    throw exn;
  }
  return more();
}

bool Scanner::scanSymbol(char c) {
  if (eof()) {
    ScanException exn(line, pos);
    exn << "End-of-input when expecting \"" << c << "\".";
    throw exn;
  }
  if (current() == c) {
    consume();
    advance();
  }
  else {
    ScanException exn(line, pos);
    exn << "Expected \"" << c << "\" but \"" << current() << "\" was found.";
    throw exn;
  }
  return more();
}

bool Scanner::scanUntil(char until) {
  /* TODO: An open issue: should we skip whitspaces here? */
  /*skipWS();*/
  while (current() != until) {
    if (current() == '\"') {
      scanString();
      continue;
    }
    if (current() == '\'' && more() && next() == '\'') {
      scanHOLString();
      continue;
    }
    if (current() == ')' || current() == ']' || current() == '}') {
      ScanException exn(line, pos);
      exn << "Encountered ill-formed parenthesis: \"" << current() << "\".";
      throw exn;
    }
    consume();
    if (eof()) {
      ScanException exn(line, pos);
      exn << "Unexpected end-of-input when scanning for \"" << until << "\".";
      throw exn;
    }
    switch (current()) {
      case '(': advance(); scanUntil(')'); consume(); advance(); break;
      case '[': advance(); scanUntil(']'); consume(); advance(); break;
      case '{': advance(); scanUntil('}'); consume(); advance(); break;
      /* Are there other kinds of parentheses we need to consider? */
      default: advance();
    }
  }
  return more();
}

/* Problem: we also should consume the string quotation marks! */

bool Scanner::scanString() {
  try {
    scanSymbol('\"');
  }
  catch (ScanException& exn) {
    exn.str("");
    exn << "Error parsing string, expecting \".";
    throw exn;
  }
  try {
    while (!(current() == '\"')) {
      consume();
      advance();
    }
    scanSymbol('\"');
  }
  catch (ScanException& exn) {
    exn.str("");
    exn << "Unexpected end-of-file when parsing string.";
    throw exn;
  }
  return more();
}

bool Scanner::scanHOLString() {
  try {
    scanSymbol('\'');
    scanSymbol('\'');
  }
  catch (ScanException& exn) {
    exn.str("");
    exn << "Error parsing HOL string, expecting \"\'\'\".";
    throw exn;
  }
  try {
    while (!(current() == '\'' && more() && next() == '\'')) {
      consume();
      advance();
    }
    scanSymbol('\'');
    scanSymbol('\'');
  }
  catch (ScanException& exn) {
    exn.str("");
    exn << "Unexpected end-of-file when parsing HOL string.";
    throw exn;
  }
  return more();
}

bool Scanner::scanTerm(char until) {
  clearToken();
  skipWS();
  scanUntil(until);
  /* Remove any trailing white-space characters from the token. */
  while (token_index > 0) {
    char c = token[token_index - 1];
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f') {
      token_index--;
    }
    else { break; }
  }
  token[token_index] = '\0';
  token_length = token_index;
  return more();
}

void Scanner::scanRelation(Symtab& symtab, MapletRecorder *mrec) {
  initScan();
  if (mrec != nullptr) mrec->initialise();
  if (advance()) {
    skipWS();
    skipSymbol('{');
    skipWS();
    while (current() != '}') {
      skipSymbol('(');
      scanTerm(',');
      /*debug << "L-Term: \"" << token << "\"" << endl;*/
      int id1 = symtab[token];
      skipSymbol(',');
      scanTerm(')');
      /*debug << "R-Term: \"" << token << "\"" << endl;*/
      int id2 = symtab[token];
      skipSymbol(')');
      if (mrec != nullptr) mrec->record(id1-1, id2-1);
      skipWS();
      if (current() != '}') {
        skipSymbol(',');
        skipWS();
      }
    }
    /* We cannot advance() here since "}" may be the last symbol. */
    /*skipSymbol('}');*/
    if (more()) {
      skipSymbol('}');
      skipWS();
    }
    if (!eof()) {
      throw ScanException(
        "Input contains additional text after \"}\".", line, pos);
    }
    if (mrec != nullptr) mrec->finalise();
  }
  else {
    throw ScanException("Input is empty.", line, pos);
  }
}
