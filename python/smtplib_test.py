import smtplib
import subprocess

p = subprocess.Popen("df -h", shell=True, stdout=subprocess.PIPE)
MSG = p.stdout.read().decode("utf-8")
FROM = "guru-python-sysadmin@example.com"
TO = "john@back"
SUBJECT = "Nightly Disk Usage Report"

msg = "\r\n".join(
    ("From: %s" % FROM, "To: %s" %TO, "Subject: %s" % SUBJECT, "", MSG)
)

server = smtplib.SMTP('localhost')
server.sendmail(FROM, TO, msg)
server.quit()

