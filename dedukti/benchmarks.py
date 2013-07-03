import os
import subprocess
import time

files = list(filter(lambda filename: filename.endswith(".dk"), os.listdir("atomic")))
files.sort(key=lambda filename: os.path.getsize("atomic/" + filename))
for filename in files:
  start = time.time()
  code = subprocess.call(["bash", "-c", "camelide atomic/%s > /dev/null 2>&1" % filename])
#  code = subprocess.call(["bash", "-c", "dkcheck atomic/%s > /dev/null 2>%1" % filename])
  end = time.time()
  if code == 0:
    print("%-30s  %10d  %04.2f" % (os.path.splitext(filename)[0], os.path.getsize("atomic/" + filename), end - start))
  else:
    print("%-30s  %10d  FAIL" % (os.path.splitext(filename)[0], os.path.getsize("atomic/" + filename)))
  
