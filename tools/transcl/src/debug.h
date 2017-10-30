#ifndef DEBUG_H
#define DEBUG_H
#include<iostream>

#include "NullStream.hpp"

/* Global variables */
extern bool debug_enabled;

#define debug (debug_enabled ? std::cerr : std::nil)

/* Function prototypes */
void enable_debug();
void disable_debug();
#endif
