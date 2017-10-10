#ifndef MAIN_H
#define MAIN_H
#include<iostream>
#include<fstream>

#include"argp_conf.h"

#define outp (file != nullptr ? (*file) : std::cout)

extern std::ofstream* file;
#endif
