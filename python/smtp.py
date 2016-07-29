import smtplib

mail_server = 'smtp.gmail.com'
mail_server_port = 26  # 26 is the wrong answer for ssl, check it

username = 'username'
password = 'password'

from_addr = 'username@gmail.com'
to_addr = 'someone@hotmail.com'
from_header = 'From: %s\r\n' % from_addr
to_header = 'To: %s\r\n\r\n' % to_addr
subject_header = 'Subject: nothing interesting'
body = 'This is not a very interesting email'
email_message = '%s\n%s\n%s\n\n%s' % (from_header, to_header, subject_header, body)

# this worked but subject line was part of the body, etc
# need to investigate API of smtplib a bit more 
s = smtplib.SMTP_SSL()
s.connect(mail_server,mail_server_port)
s.login(username, password)
s.sendmail(from_addr, to_addr, email_message)
s.quit()

print('done')
