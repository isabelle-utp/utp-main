#include "debug.h"

bool debug_enabled = false;

void enable_debug() {
  debug_enabled = true;
}

void disable_debug() {
  debug_enabled = false;
}
