import os
import subprocess
import time

files = list(filter(lambda filename: filename.endswith(".dk"), os.listdir("atomic")))
files.sort(key=lambda filename: os.path.getsize("atomic/" + filename))
for filename in files:
  start = time.time()
#  subprocess.call(["bash", "-c", "camelide atomic/%s 2> /dev/null" % filename])
  subprocess.call(["bash", "-c", "dkcheck atomic/%s 2> /dev/null" % filename])
  end = time.time()
  print("%-30s  %10d  %04.2f" % (filename, os.path.getsize("atomic/" + filename), end - start))
  
