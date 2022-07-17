#!/usr/bin/env python3
################################################################################
# Python script for local installation and compilation of Isabelle/UTP heaps   #
# Author: Frank Zeyda (frank.zeyda@gmail.com)                                  #
# Last Modified: 20/06/2022 (Frank Zeyda)                                      #
################################################################################
import sys, os, re, glob, shutil
import termios, tty
import subprocess
import argparse
import functools

# It may be more robust to directly include the code of toposort
# here rather than having the user to install it e.g. via pip.
from toposort import toposort, toposort_flatten

# The script has been tested with the following Python versions:
# - Python 3.5.2

# TODO: Ensure that it works with any Python 2.X and 3.X release.

# Requirements (packages):
# - toposort 1.7

# Globals for the script name and its directory.
SCRIPT_NAME = os.path.basename(__file__)
SCRIPT_DIR = os.path.dirname(__file__)
SCRIPT_DIR = os.path.realpath(SCRIPT_DIR)

# Global for the current version of the script.
SCRIPT_VERSION = "0.1"

# Required version of the Isabelle tool-chain.
ISABELLE_VERSION = "Isabelle2021-1"

# Name of the log file written by the build command.
BUILD_LOG = "build.log"

#####################
# Utility Functions #
#####################

# Flattens a list of lists into a single list.
def flatten(ll):
  result = []
  for l in ll:
    result.extend(l)
  return result

# Custom sort key to be used when sorting paths lists.
def path_sortkey(path):
  return path.split(os.sep)

# Removes quotes from the given string s, if present.
# Otherwise, returns the strings unchanged.
def remove_quotes(s):
  if len(s) >= 2 and s.startswith('"') and s.endswith('"'):
    return s[1:-1]
  else: return s

# Removes a given prefix from a text if present.
# Otherwise, returns the text as is.
def remove_prefix(text, prefix):
  if text.startswith(prefix):
    return text[len(prefix):]
  else: return text

# String representation of a set of strings.
def str_of_set(s):
  return "{" + ", ".join(map(str, s)) + "}"

# Checks if a given object is a string.
def isstr(o):
  return isinstance(o, str)

# Checks if a given object is a list of strings.
def isstrlist(o):
  if not isinstance(o, list):
    return False
  for e in o:
    if not isinstance(e, str):
      return False
  return True

# Checks if a given object is a dictionary of options.
def isoptdict(o):
  if not isinstance(o, dict):
    return False
  for key, value in o.items():
    if not isinstance(key, str):
      return False
    if not isinstance(value, str):
      return False
  return True

# Synchronous execution of a shell command, capturing its outputs.
def run_sync(*cmd):
  if DEBUG_OUTPUT:
    CMDLINE = " ".join(cmd)
    debug("Executing shell command: '" + ANSI.intoYellow(CMDLINE) + "'")
  process = subprocess.run(cmd, stdout = subprocess.PIPE, \
                                stderr = subprocess.PIPE)
  retcode = process.returncode
  stdout = process.stdout.decode("utf-8")
  stderr = process.stderr.decode("utf-8")
  return retcode, stdout, stderr

def remove_if_exists(fullname):
  if os.path.isfile(fullname):
    info("Deleting file: " + ANSI.intoYellow(fullname))
    os.remove(fullname)
    return True
  else: return False

# Ask a yes/no question, using a single (unbuffered) key stoke.
def ask_yes_no(text, default = 'no'):
  assert default in ['yes', 'no']
  choice = None
  while choice is None:
    print(text, end='')
    if default == 'no' : flush(" [N/y] ", end='')
    if default == 'yes': flush(" [Y/n] ", end='')
    fd = sys.stdin.fileno()
    stdin_settings = termios.tcgetattr(fd)
    try: # temporarily switch to unbuffered IO
      tty.setraw(sys.stdin.fileno())
      c = sys.stdin.read(1)
    finally: # restore buffered terminal IO
      termios.tcsetattr(fd, termios.TCSADRAIN, stdin_settings)
    switcher = {
      'n': 'no',
      'N': 'no',
      'y': 'yes',
      'Y': 'yes',
      '\x03': 'abort', # [CTRL-C]
      '\r': default
    }
    choice = switcher.get(c, None)
    if choice == 'no'   : flush(ANSI.intoRed("NO"))
    if choice == 'yes'  : flush(ANSI.intoGreen("YES"))
    if choice == 'abort': flush()
    if choice == None   : flush(c)
  if choice == 'abort': exit(1)
  return choice

#########################
# ANSI Terminal Colours #
#########################

class ANSI:
  # Strings for various ANSI escape sequences for fonts and colours.
  BLACK   = '\33[30m'
  RED     = '\33[31m'
  GREEN   = '\33[32m'
  YELLOW  = '\33[33m'
  BLUE    = '\33[34m'
  MAGENTA = '\33[35m'
  CYAN    = '\33[36m'
  WHITE   = '\33[37m'
  BOLD    = "\033[1m"
  NORMAL  = "\033[0m"

  # Global flag that enables/disables colourful terminal output.
  ENABLED = True

  @classmethod
  def __wrap__(cls, esc):
    def inner(text):
      if cls.ENABLED:
        return esc + text + cls.NORMAL
      else: return text
    return inner

  @classmethod
  def intoBlack(cls, text):
    return cls.__wrap__(cls.BLACK)(text)

  @classmethod
  def intoRed(cls, text):
    return cls.__wrap__(cls.RED)(text)

  @classmethod
  def intoGreen(cls, text):
    return cls.__wrap__(cls.GREEN)(text)

  @classmethod
  def intoYellow(cls, text):
    return cls.__wrap__(cls.YELLOW)(text)

  @classmethod
  def intoBlue(cls, text):
    return cls.__wrap__(cls.BLUE)(text)

  @classmethod
  def intoMagenta(cls, text):
    return cls.__wrap__(cls.MAGENTA)(text)

  @classmethod
  def intoCyan(cls, text):
    return cls.__wrap__(cls.CYAN)(text)

  @classmethod
  def intoWhite(cls, text):
    return cls.__wrap__(cls.WHITE)(text)

  @classmethod
  def intoBold(cls, text):
    return cls.__wrap__(cls.BOLD)(text)

####################
# Logging Messages #
####################

# Global flags to control verbose and debug output.
VERBOSE_OUTPUT = True
DEBUG_OUTPUT = True

def eprint(*args, **kwargs):
  print(*args, file = sys.stderr, **kwargs)

def flush(*args, **kwargs):
  print(*args, **kwargs)
  sys.stdout.flush()

def debug(msg):
  if DEBUG_OUTPUT:
    eprint("[" + ANSI.intoCyan("DEBUG") + "] " + msg)

def info(msg):
  if VERBOSE_OUTPUT:
    eprint("[" + ANSI.intoBlue("INFO") + "] " + msg)

def warning(msg):
  eprint("[" + ANSI.intoYellow("WARNING") + "] " + msg)

def error(msg):
  eprint("[" + ANSI.intoRed("ERROR") + "] " + msg)

def critical(msg):
  error(msg)
  eprint("-> Aborting script due to error(s) ...")
  exit(1)

###############
# Output Tags #
###############

class Tags:
  def emit_pass():
    flush("[" + ANSI.intoGreen("PASS") + "]")

  def emit_fail():
    flush("[" + ANSI.intoRed("FAIL") + "]")

  def emit_skip():
    flush("[" + ANSI.intoYellow("SKIP") + "]")

#############################
# Isabelle Tool Invocations #
#############################

class Isabelle:
  # Link to the Isabelle tool download. Reported by some error messages.
  TOOL_LINK = "https://isabelle.in.tum.de/"

  # Checks that the installed Isabelle agrees with ISABELLE_VERSION.
  @classmethod
  def check_version(cls):
    try:
      retcode, stdout, stderr = run_sync("isabelle", "version")
      if retcode == 0:
        if stdout.strip() == ISABELLE_VERSION: pass
        else: critical("Wrong version of Isabelle detected. " + \
                       "Please install " + ANSI.intoBold(TOOL_VERSION) + ".")
      else: critical("Problems running the 'isabelle version' command (?)")
    except FileNotFoundError:
      cls.NotInstalledError()

  # Builds a given session given as an object of the Session class.
  @classmethod
  def build(cls, session):
    flush("Building " + ANSI.intoBold(session.name) + " ...", end = ' ')
    # Skip building if any of the ancestors of session failed to build.
    for ancestor in session.ancestors:
      assert ancestor.built
      if not ancestor.success:
        # Print a [SKIP] tag and return.
        Tags.emit_skip()
        session.mark_skipped()
        return None
    # Execute the respective 'isabelle build ...' shell command.
    CMD = ["isabelle", "build", "-c", "-b", session.name]
    retcode, stdout, stderr = run_sync(*CMD)
    # Print a [PASS] or [FAIL] tag, depending on the return code.
    if retcode == 0:
      Tags.emit_pass()
    else:
      Tags.emit_fail()
    # Show shell command output if verbose output is requested.
    if VERBOSE_OUTPUT:
      if stdout.strip():
        info("Output to <" + ANSI.intoBold("stdout") + ">:")
        eprint(ANSI.intoYellow(stdout))
      if stderr.strip():
        info("Output to <" + ANSI.intoBold("stderr") + ">:")
        eprint(ANSI.intoRed(stderr))
    # Added information to the session object about the build.
    session.status = {}
    session.status['built'] = True
    session.status['success'] = (retcode == 0)
    session.status['skipped'] = False
    session.status['retcode'] = retcode
    session.status['stdout'] = stdout
    session.status['stderr'] = stderr
    # Return True if the session was built successful; otherwise False.
    return retcode == 0

  @classmethod
  def ISABELLE_HOME(cls):
    try:
      CMD = ["isabelle", "getenv", "-b", "ISABELLE_HOME"]
      retcode, stdout, stderr = run_sync(*CMD)
      if retcode == 0:
        return stdout.strip()
      else:
        CMD_LINE = ANSI.intoBold(" ".join(CMD))
        critical("Problems running the '" + CMD_LINE + "' command.")
    except FileNotFoundError:
      cls.NotInstalledError()

  @classmethod
  def ISABELLE_USER_HOME(cls):
    try:
      CMD = ["isabelle", "getenv", "-b", "ISABELLE_HOME_USER"]
      retcode, stdout, stderr = run_sync(*CMD)
      if retcode == 0:
        return stdout.strip()
      else:
        CMD_LINE = ANSI.intoBold(" ".join(CMD))
        critical("Problems running the '" + CMD_LINE + "' command.")
    except FileNotFoundError:
      cls.NotInstalledError()

  @classmethod
  def NotInstalledError(cls):
    critical("Isabelle seems not to be installed. " + \
      "Please download and install " + TOOL_VERSION + \
      " from " + ANSI.intoBold(cls.TOOL_LINK) + ".")

##################
# Isabelle Heaps #
##################

class Heaps:

  @classmethod
  def get_user_heap_dir(cls):
    ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
    GLOB_PATTERN = os.path.join(ISABELLE_USER_HOME, "heaps", "*")
    HEAP_DIRS = glob.glob(GLOB_PATTERN)
    if len(HEAP_DIRS) == 0:
      critical("Failed to located user directory for heaps.")
    elif len(HEAP_DIRS) > 1:
      critical("Multiple user directories for heaps found: " + \
               ANSI.intoBold(" ".join(HEAP_DIRS)))
    else:
      return HEAP_DIRS[0]

  @classmethod
  def get_user_heap_files(cls):
    HEAP_FILES = []
    HEAP_DIR = cls.get_user_heap_dir()
    for filename in os.listdir(HEAP_DIR):
      fullname = os.path.join(HEAP_DIR, filename)
      if os.path.isfile(fullname):
        # Check that the file starts with 'POLYSAVE'.
        with open(fullname, 'rb') as file:
          magic_number = file.read(8).decode("utf-8")
          if magic_number == 'POLYSAVE':
            HEAP_FILES.append(filename)
    return HEAP_FILES

#################################
# Light-weight ROOT File Parser #
#################################

# The parsers is based on Python regular expressions and therefore
# might not detect all errors in the input or deal with the precise
# syntax of ROOT files, albeit making the best effort to do so.
# We note that the parser can also deal with nested comment blocks.

# A known ramification is related to having multiple theories,
# document_files and export_files sections per session. The ROOT
# grammar allows this, however, our parsers does not. An exception
# is that two theories sections are permitted if they abide to the
# following format:
#   theories [document = false]
#     ...
#   theories
#     ...
# Having full support for multiple theories sections may push the
# limits of using regular expression for parsing the ROOT files...

# Keywords recognised by the parser.
KEYWORDS = [
  "session",
  "in",
  "description",
  "options",
  "sessions",
  "directories",
  "theories",
  "document_theories",
  "document_files",
  "export_files"
]

# Negative assertion ensuring that the subsequent text is *not* a keyword.
BLOCK_KEYWORD = r'(?!' + r'|'.join(KEYWORDS) + ')'

# Regular expression for a (possibly quoted) name.
def NAME_REGEX(group):
  return r'(?P<' + group + r'>' + BLOCK_KEYWORD + '\w+|"[^"]*")'

# Regular expression for a list of (possibly quoted) names.
# Note that names must be separated by one or more whitespaces.
# Keywords occurring inside the KEYWORDS global are not parsed.
def NAMES_REGEX(group):
  return r'(?P<' + group + r'>\s*(?:(' + BLOCK_KEYWORD + '\w+|"[^"]*")\s*)*)'

# Regular expression for a single option.
# The key and value are parsed as names.
OPTION_REGEX = \
  NAME_REGEX('key') + r'\s*=\s*' + NAME_REGEX('value')

# Regular expression for the options clause.
# Note that we do not parse/check the content of [...] here.
OPTIONS_REGEX = r'\[(?P<options>[^\]]*)\]'

# Regular expression for parsing a session entry.
SESSION_REGEX = \
  r'session\s+'                    + NAME_REGEX('session')                 + \
  r'\s*' + r'(?:\('                + NAMES_REGEX('groups')      + r'\))?'  + \
  r'\s*' + r'(?:in\s+'             + NAME_REGEX('directory')    + r')?'    + \
  r'\s*' + r'=\s*'                 + NAME_REGEX('parent')       + r'\s*\+' + \
  r'\s*' + r'(?:description\s+'    + NAME_REGEX('description')  + r')?'    + \
  r'\s*' + r'(?:options\s*'        + OPTIONS_REGEX              + r')?'    + \
  r'\s*' + r'(?:sessions\s+'       + NAMES_REGEX('sessions')    + r')?'    + \
  r'\s*' + r'(?:directories\s+'    + NAMES_REGEX('directories') + r')?'    + \
  r'\s*' + r'(?:theories(?:\s*\[\s*document\s*=\s*false\s*\]\s*)'        \
                                   + NAMES_REGEX('theories1')   + r')?'    + \
  r'\s*' + r'(?:theories\s+'       + NAMES_REGEX('theories2')   + r')?'    + \
  r'\s*' + r'(?:document_theories\s+' + NAMES_REGEX('document_theories') + r')?' + \
  r'\s*' + r'(?:document_files\s+' + NAMES_REGEX('document_files') + r')?' + \
  r'\s*' + r'(?:export_files\s+'   + NAMES_REGEX('export_files')   + r')?'

# Regular expression for removing comments in ROOT files.
# Observe the negative lookahead assertions below. It prevent unwanted
# matching of nested comment parentheses. We deal with nested comments
# by iteratively applying the pattern until no more changes occur.
REMOVE_COMMENTS_REGEX = r'(?s)\(\*((?!\(\*)(?!\*\)).)*\*\)'

# Extracts session, theory, etc. names from the text following the keyword.
def extract_names(names):
  result = []
  if names is not None:
    for match in re.finditer(NAME_REGEX('name'), names, re.ASCII):
      name = match.group('name')
      name = remove_quotes(name)
      result.append(name)
  return result

# Extracts options from the content of the "options [...]" clause.
def extract_options(options):
  result = {}
  if options is not None:
    for match in re.finditer(OPTION_REGEX, options, re.ASCII):
      key = match.group('key')
      key = remove_quotes(key)
      value = match.group('value')
      value = remove_quotes(value)
      result[key] = value
  return result

# Loads ROOT file under the given path and returns its content.
def load_ROOT(rootpath):
  ROOTFILE = os.path.join(rootpath, 'ROOT')
  if os.path.isfile(ROOTFILE):
    info("Loading file '{}'".format(ROOTFILE))
    with open(ROOTFILE) as file:
      content = file.read()
    return content
  else: return None

# Loads a ROOT file under the given path and parses its content.
# As a result of calling this function, session_dict is extended
# with new entries for the sessions found in ROOT. These entries
# map the session's name to an instance of the Session class.
def parse_ROOT(rootpath, session_dict):
  content = load_ROOT(rootpath)
  if content is not None:
    # Remove (* ... *) comments from content.
    prev_content = None
    while prev_content != content:
      prev_content = content
      content = re.sub(REMOVE_COMMENTS_REGEX, "", content)
    # Match all occurrences of SESSION_REGEX.
    for match in re.finditer(SESSION_REGEX, content, re.ASCII):
      name = match.group('session')
      name = remove_quotes(name)
      groups = extract_names(match.group('groups'))
      directory = match.group('directory') or '"."'
      directory = remove_quotes(directory)
      parent = match.group('parent')
      parent = remove_quotes(parent)
      options = extract_options(match.group('options'))
      sessions = extract_names(match.group('sessions'))
      directories = extract_names(match.group('directories'))
      theories1 = extract_names(match.group('theories1'))
      theories2 = extract_names(match.group('theories2'))
      theories = theories1 + theories2
      document_theories = extract_names(match.group('document_theories'))
      document_files = extract_names(match.group('document_files'))
      export_files = extract_names(match.group('export_files'))
      session = Session(rootpath, name, groups, directory, parent, options, \
        sessions, directories, theories, document_theories, document_files, \
        export_files)
      if name in session_dict.keys():
        critical("Duplicate entries for session " + name + " in ROOT file(s).")
      session_dict[name] = session
  else: warning("No ROOT file found under '" + rootpath + "'")

#################
# Session Class #
#################

@functools.total_ordering
class Session:

  # Constructor of the Session class
  def __init__(self, rootpath, session, groups, directory, parent,  \
      options = [], sessions = [], directories = [], theories = [], \
      document_theories = [], document_files = [], export_files = []):
    # Verify the type of each arguments.
    assert isstr(rootpath)
    assert isstr(session)
    assert isstrlist(groups)
    assert isstr(directory)
    assert isstr(parent)
    assert isoptdict(options)
    assert isstrlist(sessions)
    assert isstrlist(directories)
    assert isstrlist(theories)
    assert isstrlist(document_theories)
    assert isstrlist(document_files)
    assert isstrlist(export_files)
    # Assign each arguments to a public field.
    self.rootpath = rootpath
    self.name = session
    self.groups = groups
    self.directory = directory
    self.parent = parent
    self.options = options
    self.sessions = sessions
    self.directories = directories
    self.theories = theories
    self.document_theories = document_theories
    self.document_files = document_files
    self.export_files = export_files
    # The below field is used as an index to order sessions.
    # It is collaterally initialised by the Sessions.load()
    # method, namely to a pair of integer index values that
    # encode the structure of Sessions.TSETS topological sort.
    self.ordinal = None
    # Indicates that the session has not been built so far.
    self.reset_status()

  # Reset the session status to not built yet.
  def reset_status(self):
    self.status = {}
    self.status['built'] = False
    self.status['skipped'] = None
    self.status['success'] = None
    self.status['retcode'] = None
    self.status['stdout'] = None
    self.status['stderr'] = None

  # Mark the session as skipped during a build.
  def mark_skipped(self):
    self.status = {}
    self.status['built'] = True
    self.status['skipped'] = True
    self.status['success'] = None
    self.status['retcode'] = None
    self.status['stdout'] = None
    self.status['stderr'] = None

  @property
  def built(self):
    return self.status['built']

  @property
  def skipped(self):
    return self.status['skipped']

  @property
  def success(self):
    return self.status['success']

  @property
  def retcode(self):
    return self.status['retcode']

  @property
  def stdout(self):
    return self.status['stdout']

  @property
  def stderr(self):
    return self.status['stderr']

  # Returns the list of absolute paths used for locating theories.
  @property
  def theory_paths(self):
    paths = [self.directory]
    for d in self.directories:
      paths.append(os.path.join(self.directory, d))
    paths = map(lambda d: os.path.join(self.rootpath, d), paths)
    paths = map(os.path.realpath, paths)
    return list(paths)

  # Attempts to load the file for a given theory of the session.
  # The function returns two values: the full canonical file path
  # of the resp. loaded .thy file and its content as a string.
  # If the loading fails, 'None, None' is returned instead.
  def load_theory(self, theory):
    thy_file = theory + ".thy"
    for path in self.theory_paths:
      fullpath = os.path.join(path, thy_file)
      fullpath = os.path.realpath(fullpath)
      if os.path.isfile(fullpath):
        with open(fullpath) as thy:
          return fullpath, thy.read()
    return None, None

  # Determines all transitive ancestors sessions of this session.
  @property
  def ancestors(self):
    ancestors = set()
    # Local functions to add the direct ancestors of a given session
    # to the above 'ancestors' variable. This avoid code duplication.
    def add_ancestors(session):
      names = [session.parent] + session.sessions
      for name in names:
        if Sessions.lookup(name) is not None:
          ancestors.add(Sessions.lookup(name))
    # Initially, include only the direct ancestors of session self.
    add_ancestors(self)
    # Next, iterative add all ancestors of any of the sessions in
    # 'ancestors'. Proceed with this until 'ancestors' has converged.
    changed = True
    while changed:
      before = ancestors.copy()
      for ancestor in ancestors.copy():
        add_ancestors(ancestor)
      after = ancestors.copy()
      changed = (before != after)
    return ancestors

  # Write log entry for this session after it has been built.
  def write_log(self, filename):
    def heading(stream, text):
      HLINE = "-" * 80 # string used for a horizontal line in ASCII
      stream.write(HLINE + "\n")
      stream.write(text  + "\n")
      stream.write(HLINE + "\n")
    if self.built:
      with open(filename, 'a') as log:
        heading(log, "Session: " + self.name + " " + self.__tag__())
        if self.skipped:
          # Collect ancestors that failed to built and report them.
          failed = [s.name for s in self.ancestors if \
                    s.built and not s.skipped and not s.success]
          log.write("Skipping " + self.name + " due to " + \
            str_of_set(failed) + " failing to build.\n")
        else:
          # Write stdout output of isabelle build if present.
          if len(self.stdout.strip()) > 0:
            log.write(self.stdout)
            if not self.stdout.endswith("\n"):
              log.write("\n")
          # Write stderr output of isabelle build if present.
          if len(self.stderr.strip()) > 0:
            log.write(self.stderr)
            if not self.stderr.endswith("\n"):
              log.write("\n")

  # Generate a result tag for this session.
  def __tag__(self):
    if self.built:
      if self.skipped:
        return "[SKIPPED]"
      else:
        return "[PASS]" if self.success else "[FAIL]"
    else:
      return "[NOT BUILT]"

  # Equality test of Session objects.
  def __eq__(self, other):
    if type(self) == type(other):
      return self.name == other.name
    else: return False

  # Comparison of Session objects.
  def __lt__(self, other):
    if type(self) == type(other):
      return self.ordinal < other.ordinal
    else: return False

  # Hash value of a Session object.
  def __hash__(self):
    return hash(self.name)

  # String representation; this is just the name of the session.
  def __str__(self):
    return self.name

##################
# Sessions Class #
##################

class Sessions:
  # Holds the global dictionary of Session objects.
  DICT = None

  # Holds a topologically sorted list of Session objects.
  # This is according to their dependency relation.
  TLIST = None

  # Holds a topologically sorted list of Session objects.
  # This is according to their dependency relation.
  # Here, the elements are sets rather than a flat list;
  # sessions in each set are independent of each other.
  TSETS = None

  # Load and all ROOT files and parse their sessions.
  # The static method initialises DICT, TLIST and TSETS
  # and also the respective ordering on Session objects.
  @classmethod
  def load(cls, top_folder):
    cls.DICT = {}
    for path, dirnames, filenames in os.walk(top_folder):
      if 'ROOT' in filenames:
        parse_ROOT(path, cls.DICT)
    tsort, tsort_flat = create_session_toposort(cls.DICT.values())
    cls.TLIST = list(map(cls.lookup, tsort_flat))
    cls.TSETS = list(map(lambda ss: set(map(cls.lookup, ss)), tsort))
    cls.__init_session_order__()

  # Initialises an ordering all session objects recorded in TSETS.
  # This is according to the topological sorting of sessions therein.
  # The session's ordinal fields are therefore set, namely to a pair
  # of integers (group-index, session-index). Sessions in the same
  # group are independent and can therefore be built in parallel.
  # Indices of both components of the pair start counting from one.
  @classmethod
  def __init_session_order__(cls):
    group_index = 1
    for group in cls.TSETS:
      session_index = 1
      for session in group:
        session.ordinal = (group_index, session_index)
        session_index += 1
      group_index += 1

  # Resets the compilation status of all loaded sessions.
  @classmethod
  def reset(cls):
    for session in cls.DICT.values():
      session.reset_status()

  # Checks if a session with a given name exists.
  @classmethod
  def exists(cls, name):
    return cls.lookup(name) is not None

  # Looks up a session by its name, using Sessions.DICT.
  # Returns None if no session with the given name is present.
  @classmethod
  def lookup(cls, name):
    assert isstr(name)
    return cls.DICT.get(name)

  # Returns a list of all session names of loaded sessions.
  @classmethod
  def names(cls):
    return [s.name for s in cls.TLIST]

  # Returns a list of all root directories of loaded sessions.
  @classmethod
  def rootpaths(cls):
    rootpaths = {os.path.realpath(s.rootpath) for s in cls.TLIST}
    rootpaths = sorted(rootpaths, key = path_sortkey)
    return rootpaths

##########################
# Session Analysis Tools #
##########################

# Regular expressions to extract imported theories from .thy files.
IMPORTS_REGEX = r'(?:\s)imports\s+(?P<imports>((?!\s(begin|keywords)\s).)*)'

# Uses a best effort strategy to infer all .thy files directly used
# by a given session. This involves parsing of the imports .thy files.
def imported_thy_files_aux(session, theory, seen, failed, paths):
  if theory not in seen:
    seen.add(theory)
    fullpath, content = session.load_theory(theory)
    if fullpath in paths: return
    if content is not None:
      paths.add(fullpath)
      debug("Extracting imports for theory: " + ANSI.intoBold(theory))
      match = re.search(IMPORTS_REGEX, content, re.ASCII | re.DOTALL)
      if match is not None:
        imports = match.group('imports')
        # One iteration of replacement ought be sufficient here.
        imports = re.sub(REMOVE_COMMENTS_REGEX, "", imports)
        imports = imports.strip()
        for match in re.finditer(NAME_REGEX('name'), imports, re.ASCII):
          imported_theory = match.group('name')
          imported_theory = remove_quotes(imported_theory)
          imported_thy_files_aux(session, imported_theory, seen, failed, paths)
      else: warning( \
        "Failed to extract imports of theory: " + ANSI.intoBold(theory))
    else: failed.add(theory)

# Attempts to infer all .thy files used by the given session.
def imported_thy_files(session):
  seen, failed, paths = set(), set(), set()
  info("Deducing theories for session: " + ANSI.intoBold(session.name))
  info("Top-level theories: " + str_of_set(session.theories))
  for theory in session.theories:
    imported_thy_files_aux(session, theory, seen, failed, paths)
  if len(failed) > 0:
    failed = sorted(failed)
    info("Failed to locate theory files for: " + str_of_set(failed))
  return sorted(paths, key = path_sortkey)

# Attempts to infer all .thy files used by all loaded sessions.
def all_imported_thy_files():
  result = set()
  for session in Sessions.TLIST:
    thyfiles = imported_thy_files(session)
    result.update(thyfiles)
  return sorted(result, key = path_sortkey)

###################################
# Topological Sorting of Sessions #
###################################

# Since we do not want to parse the Isabelle installation ROOT file,
# we add some relevant default dependencies here. Perhaps this is not
# a totally satisfactory solution ...
DEFAULT_GRAPH = {
  'HOL-Algebra': ['HOL'],
  'HOL-Cardinals': ['HOL'],
  'HOL-Eisbach': ['HOL']
}

# Creates a graph (dictionary) from a given list of sessions.
# The graph captures the direct dependency between sessions
# and is encoded by a dictionary of strings to string lists.
def create_session_graph(sessions):
  graph = DEFAULT_GRAPH.copy()
  for session in sessions:
    graph[session.name] = [session.parent] + session.sessions
  return graph

# Create topological sorting of sessions (deep and flat).
# Note that this functions return structures of session
# names (strings) rather than the underlying Session objects.
def create_session_toposort(sessions):
  names = {s.name for s in sessions}
  graph = create_session_graph(sessions)
  tsort = list(toposort(graph))
  # Remove sessions that merely appear as dependencies.
  for group in tsort:
    group.intersection_update(names)
  # Remove emerging empty sets from the above step.
  tsort = list(filter(lambda s: len(s) != 0, tsort))
  tsort_flat = flatten(tsort)
  return tsort, tsort_flat

###################
# Argument Parser #
###################

# TODO: I am still a bit unsure how to use the run command. I imagine
# something like: "./isabelle-utp.py run tutorial" which will then start
# the general tutorial, invoking isabelle jedit with suitable arguments
# to open the respective theories and root session. The install command
# should not just add components via "isabelle components -u ..." but
# also give the user the option to directly download precompiled heaps
# from GitHub. This would largely simplify and speed up the installation
# process --- we cannot really expect users to compile all the heaps as
# this make take several hours...

COMMANDS = [
  'install',   # [WIP]
  'uninstall', # [WIP]
  'clean',     # [DONE]
  'build',     # [DONE]
  'release',   # [TODO]
  'run',       # [TODO]
  'sessions',  # [DONE]
  'theories',  # [DONE]
  'orphans'    # [DONE]
]

# TODO: The description needs to be elaborated, explaining all commands.
ARG_PARSER = argparse.ArgumentParser(description =
  'Isabelle/UTP installation and compilation utility.')

# TODO: I am not happy with formatting of the --help text. I understand
# there is an API to have more control over this; explore this before
# the first release of the script.

ARG_PARSER.add_argument('cmd', metavar = 'CMD', type = str,
  help = 'command to be executed. Possible commands are: ' + \
    ', '.join(map(ANSI.intoBold,COMMANDS[0:-1])) + ' and ' + \
                  ANSI.intoBold(COMMANDS[-1]) + '.')

ARG_PARSER.add_argument('-s', '--session', dest = 'session', \
  help = 'provide session to be analysed by the the ' + \
             ANSI.intoBold('theories') + ' command. ' + \
         'If absent, the theory files of ' + ANSI.intoBold('all')  + \
         ' local sessions will be deduced and printed.')

ARG_PARSER.add_argument('-n', '--no-color', dest = 'color',
  default = True, action = 'store_false',
  help = 'disable ANSI terminal colors in output')

ARG_PARSER.add_argument('-v', '--verbose', dest = 'verbose',
  default = False, action = 'store_true',
  help = 'enable verbose output')

ARG_PARSER.add_argument('-d', '--debug', dest = 'debug',
  default = False, action = 'store_true',
  help = 'enable debug output (implies verbose)')

# TODO: Add an argument to specify a file for ignored/skipped sessions.

# Global for parsed command-line arguments.
# Initialised by a call to parse_args().
ARGS = None

# Parse command-line arguments.
# Returns arguments objects and moreover initialises the ARGS global.
def parse_args():
  global VERBOSE_OUTPUT, DEBUG_OUTPUT
  global ARGS
  ARGS = ARG_PARSER.parse_args()
  # Enables/disable ANSI terminal colours.
  ANSI.ENABLED = ARGS.color
  # Set global for verbose and debug output.
  VERBOSE_OUTPUT = ARGS.verbose or ARGS.debug
  DEBUG_OUTPUT = ARGS.debug
  return ARGS

#################
# Main Function #
#################

def not_yet_implemented():
  critical("Command '" + ANSI.intoBold(ARGS.cmd) + "' is not yet implemented!")

def backup_components():
  ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
  filename = os.path.join(ISABELLE_USER_HOME, 'etc', 'components')
  if os.path.isfile(filename):
    info("Backing up file: " + ANSI.intoYellow(filename))
    shutil.copy(filename, filename + "~")
  else: critical(
    "Failed to locate Isabelle config file: " + ANSI.intoBold(filename) + ".")

def read_components():
  ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
  filename = os.path.join(ISABELLE_USER_HOME, 'etc', 'components')
  if os.path.isfile(filename):
    components = []
    info("Reading file: " + ANSI.intoYellow(filename))
    with open(filename, "r") as file:
      for line in file.readlines():
        components.append(line.strip())
    return components
  else: critical(
    "Failed to locate Isabelle config file: " + ANSI.intoBold(filename) + ".")

def write_components(components):
  ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
  filename = os.path.join(ISABELLE_USER_HOME, 'etc', 'components')
  if os.path.isfile(filename):
    info("Writing file: " + ANSI.intoYellow(filename))
    with open(filename, "w") as file:
      for component in components:
        component = component.strip()
        # TODO: Warn here if the component directory does not exist?
        if len(component) > 0:
          file.write(component + os.linesep)
  else: critical(
    "Failed to locate Isabelle config file: " + ANSI.intoBold(filename) + ".")

def main():
  # Parse command-line arguments first, so that errors are reported.
  args = parse_args()

  # Check that the correct Isabelle tool version is installed.
  Isabelle.check_version()

  # Load sessions from all ROOT files below the script's location.
  Sessions.load(os.path.realpath(SCRIPT_DIR))
  # Sessions.load('axiomatic') # for testing ...

  # Installs Isabelle/UTP components and heaps for the current user.
  if args.cmd == 'install':
    components = read_components()
    rootpaths = Sessions.rootpaths()
    components_modified = False
    for rootpath in rootpaths:
      if rootpath not in components:
        flush("Adding component: " + ANSI.intoYellow(rootpath))
        debug("Adding '" + rootpath + "' to components.")
        components.append(rootpath)
        components_modified = True
      else:
        debug("Not adding '" + rootpath + "' to components, already present.")
    if components_modified:
      ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
      components_file = os.path.join(ISABELLE_USER_HOME, 'etc', 'components')
      flush("Updating file: " + ANSI.intoBold(components_file))
      backup_components()
      write_components(components)
    else: warning("Isabelle/UTP components seem to be already installed.")

  # Uninstalls Isabelle/UTP components and heaps for the current user.
  elif args.cmd == 'uninstall':
    retained_components = []
    components = read_components()
    rootpaths = Sessions.rootpaths()
    components_modified = False
    for component in components:
      if component in rootpaths:
        debug("Removing '" + component + "' from components.")
        components_modified = True
      else:
        retained_components.append(component)
    if components_modified:
      ISABELLE_USER_HOME = Isabelle.ISABELLE_USER_HOME()
      components_file = os.path.join(ISABELLE_USER_HOME, 'etc', 'components')
      flush("Updating file: " + ANSI.intoBold(components_file))
      backup_components()
      write_components(retained_components)
    else: warning("Isabelle/UTP seems not to be installed, nothing to do.")

  # Deletes all related heap files for any of the session in one
  # of the subordinate ROOT files. This includes the log files.
  elif args.cmd == 'clean':
    HEAP_DIR = Heaps.get_user_heap_dir()
    HEAP_FILES = Heaps.get_user_heap_files()
    heaps_to_delete = []
    for name in Sessions.names():
      if name in HEAP_FILES:
        heaps_to_delete.append(name)
    warning("The following sessions will be purged from the user's " + \
            ANSI.intoBold("heaps") + " folder: ")
    flush(" ".join(heaps_to_delete))
    # Ask the user to confirm the deletion of the heaps.
    confirm = ask_yes_no("Are you sure you like to proceed?")
    if confirm == 'yes':
      success = True
      for name in heaps_to_delete:
        fullpath_heap = os.path.join(HEAP_DIR, name)
        fullpath_log_db = os.path.join(HEAP_DIR, "log", name + ".db")
        fullpath_log_gz = os.path.join(HEAP_DIR, "log", name + ".gz")
        success = success and remove_if_exists(fullpath_heap)
        success = success and remove_if_exists(fullpath_log_db)
        success = success and remove_if_exists(fullpath_log_gz)
      flush("Successfully deleted the respective heap files.")
    else:
      flush("-> Aborting operation, no files were deleted!")
      exit(1)

  # Builds the heaps and documents for all sessions, producing useful
  # terminal outputs meanwhile as well as a log file (build.log).
  # TODO: Gather timing information for the cumulative build.
  # Also, write this information to the terminal and log file.
  elif args.cmd == 'build':
    success = True
    # Remove build.log file prior to running the build.
    run_sync("rm", "-f", BUILD_LOG)
    stage = 1
    stages = len(Sessions.TSETS)
    for group in Sessions.TSETS:
      names = str_of_set(group)
      flush("Building stage ({0}/{1}): {2}".format(stage, stages, names))
      # TODO: Currently, all sessions within a group are built
      # sequentially. However we may potentially build them
      # in parallel since they are independent of each other.
      # Explore whether Isabelle permits this and implement it!
      for session in group:
        result = Isabelle.build(session)
        success = success and bool(result)
        session.write_log(BUILD_LOG)
      stage += 1
    if success:
      flush("All sessions built successfully.")
    else:
      flush("Some sessions " + ANSI.intoBold("failed") + " to build!")

  # This command is intended to provide a unified way to start
  # isabelle jedit for various demos and tutorials supplied with
  # Isabelle/UTP. I am not sure yet about the parametrisation.
  elif args.cmd == 'run':
    not_yet_implemented()

  # Prints all sessions in topological order (one session per line).
  elif args.cmd == 'sessions':
    for session in Sessions.TLIST:
      print(session.name)

  # Print theories used by a particular session or all of them.
  elif args.cmd == 'theories':
    if args.session is None:
      thyfiles = all_imported_thy_files()
    else:
      session = Sessions.lookup(args.session)
      if session is not None:
        thyfiles = imported_thy_files(session)
      else:
        critical("Session " + ANSI.intoBold(args.session) + \
                 " not found in any of the local ROOT files.")
    for thyfile in thyfiles:
      thyfile = remove_prefix(thyfile, SCRIPT_DIR)
      thyfile = remove_prefix(thyfile, '/')
      print(thyfile)

  # Print orphan theories of a particular session or all of them.
  elif args.cmd == 'orphans':
    # First, construct the set of orphans wrt to *all* sessions.
    # This reduces false positive when calculating the orphans for
    # a particular session, that is via the --session option.
    warning("The list of orphaned theories may contain false positives.")
    thyfiles = all_imported_thy_files()
    orphans = set()
    for path, dirnames, filenames in os.walk(SCRIPT_DIR):
      for filename in filenames:
        if filename.endswith(".thy"):
          fullname = os.path.join(path, filename)
          fullname = os.path.realpath(fullname) # robustness
          if fullname not in thyfiles:
            orphans.add(fullname)
    orphans = sorted(orphans, key = path_sortkey)
    # Next, either report the complete set or the orphans or
    # those for a particular session, as per command options.
    if args.session is not None:
      session = Sessions.lookup(args.session)
      if session is None:
        critical("Session " + ANSI.intoBold(args.session) + \
                 " not found in any of the local ROOT files.")
      thyfiles = imported_thy_files(session)
      session_orphans = set()
      for search_folder in session.theory_paths:
        for path, dirnames, filenames in os.walk(search_folder):
          for filename in filenames:
            if filename.endswith(".thy"):
              fullname = os.path.join(path, filename)
              fullname = os.path.realpath(fullname) # robustness
              if fullname in orphans:
                session_orphans.add(fullname)
      session_orphans = sorted(session_orphans, key = path_sortkey)
      for orphan in session_orphans:
        orphan = remove_prefix(orphan, SCRIPT_DIR)
        orphan = remove_prefix(orphan, '/')
        print(orphan)
    else:
      for orphan in orphans:
        orphan = remove_prefix(orphan, SCRIPT_DIR)
        orphan = remove_prefix(orphan, '/')
        print(orphan)

  # Illegal command, abort script with a suitable error message.
  else:
    assert args.cmd not in COMMANDS
    error("Unknown command '" + ANSI.intoBold(args.cmd) + "'")
    eprint("Execute " + SCRIPT_NAME + " --help for usage information.")
    exit(1)

###############
# Entry Point #
###############

if __name__ == "__main__": main()
