#include<iostream>
#include"Symtab.hpp"

using namespace std;

void symtab_test() {
  Symtab symtab;
  symtab["Frank"];
  symtab["Alessi"];
  symtab["Frank"];
  symtab["Kerstin"];
  symtab["Alessi"];
  symtab["Frank"];
  symtab["Kerstin"];
  symtab["Horst"];
  symtab["Frunk"];
  symtab["Frunk"];
  symtab.print(cout);
  cout << symtab[1] << " ";
  cout << symtab[2] << " ";
  cout << symtab[3] << " ";
  cout << symtab[4] << " ";
  cout << symtab[5] << endl;
}
