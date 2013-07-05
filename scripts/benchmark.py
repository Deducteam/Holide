#!/usr/bin/env python

import os
import subprocess
import time
import sys

def basename(filename):
  return os.path.splitext(os.path.basename(filename))[0]

command = sys.argv[1]
files = sys.argv[2:]

# Maximum widh of the names to display
width = max(map(len, map(basename, files))) 
files.sort(key=os.path.getsize)
for filename in files:
  name = basename(filename)
  size = os.path.getsize(filename)
  start = time.time()
  code = subprocess.call(["bash", "-c", "%s %s > /dev/null 2>&1" % (command, filename)])
  end = time.time()
  if code == 0:
    print("%-*s  %10d  %04.2f" % (width, name, size, end - start))
  else:
    print("%-*s  %10d  FAIL" % (width, name, size))
  
