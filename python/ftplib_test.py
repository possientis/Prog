import ftplib
import sys
from ftplib import FTP
from optparse import OptionParser

parser = OptionParser()

parser.add_option("-a", "--remote_host_address", dest="remote_host_address",
        help="REMOTE FTP HOST.", default='localhost',
        metavar="REMOTE FTP HOST")

parser.add_option("-r", "--remote_file", dest="remote_file",
        help="REMOTE FILE NAME to download.",
        metavar="REMOTE FILE NAME")

parser.add_option("-l", "--local_file", dest="local_file",
        help="LOCAL FILE NAME to save remote file to", metavar="LOCAL FILE NAME")

parser.add_option("-u", "--username", dest="username",
        help="USERNAME for ftp server", metavar="USERNAME")


parser.add_option("-p", "--password", dest="password",
        help="PASSWORD for ftp server", metavar="PASSWORD")

(options, args) = parser.parse_args()

print('options: %s, args: %s' % (options, args))

if not (options.remote_file and options.local_file):
    parser.error('LOCAL FILE NAME and REMOTE FILE NAME are mandatory')

if options.username and not options.password:
    parser.error('PASSWORD is mandatory if USERNAME is present')

print("attempting to establish ftp connection to %s" % options.remote_host_address)

ftp = FTP(options.remote_host_address)

print("connection established succesfully")

if options.username:
    try:
        print("attempting to login as %s" % options.username)
        ftp.login(options.username, options.password)
        print("login was succesful")
    except ftplib.error_perm as e:
        print("Login failed: %s" % e)
        sys.exit(1)
else:
    try:
        print("attempting to login anonymously")
        ftp.login()
        print("login was succesful")
    except ftplib.error_perm as e:
        print("Anonymous login failed: %s" % e)
        sys.exit(1)

try:
    local_file = open(options.local_file, 'wb')
    ftp.retrbinary('RETR %s' % options.remote_file, local_file.write)
finally:
    local_file.close()
    ftp.close()

