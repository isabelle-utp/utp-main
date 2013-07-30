#!/usr/bin/python

import sys
import re

if len(sys.argv) < 2:
  print "Please supply a filename to process"
  sys.exit()

content = open(sys.argv[1], "r").read()

finds = re.findall('\\\\isacommand{theorem}.*%\n[^%]*',content)

print('\n<p>There are currently ' + str(len(finds)) + ' laws in this theory</p>\n')

print('\n\n'.join(map(lambda x: "<p>\n$" + x + "$\n</p>", finds)))
