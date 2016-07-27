import imaplib

username = "rob_alice"
password = "5654%^&25653t5wds^"

mail_server = "imap.gmail.com"

i = imaplib.IMAP4_SSL(mail_server)
print(i.login(username,password))
print(i.select('INBOX'))
for msg_id in i.search(None,'ALL')[1][0].split():
    print(msg_id)
    outf = open('%s.eml' % msg_id, 'w')
    outf.write(str(i.fetch(msg_id, '(RFC822)')[1][0][1]))
    outf.close()

i.logout()
