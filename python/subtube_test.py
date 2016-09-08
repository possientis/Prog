from subtube import Runner


r = Runner("df -k", "du -h /tmp", "ls -l", verbose=True, delay=5)
r.run()
