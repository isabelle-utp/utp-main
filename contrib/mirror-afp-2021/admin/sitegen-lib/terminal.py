from __future__ import print_function
from sys import stderr
from termcolor import colored

from config import options

def warn(message):
    print(colored(u"Warning: {0}".format(message), 'yellow', attrs=['bold']), file=stderr)

def error(message, exception=None, abort=False):
    print(colored(u"Error: {0}".format(message), 'red', attrs=['bold']), file=stderr)
    if exception:
        error("*** exception message:")
        error(u"*** {0!s} {1!s}".format(exception, type(exception)))
    if abort:
        error("Fatal. Aborting")
        exit(1)

def success(message):
    print(colored("Success: {0}".format(message), 'green'), file=stderr)
