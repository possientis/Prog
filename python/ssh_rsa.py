# ssh connection with RSA key
# this fails when RSA private key is encrypted (as it should be)

import paramiko

hostname = '192.168.1.xxx'
port = 22
username = 'xxx'
pkey_file = '/home/xxx/.ssh/xxx' 


if __name__ == "__main__":
    key = paramiko.RSAKey.from_private_key_file(pkey_file)
    s = paramiko.SSHClient()
    s.set_missing_host_key_policy(paramiko.AutoAddPolicy()) 
    s.load_system_host_keys()
    s.connect(hostname, port, pkey=key)
    stdin, stdout, stderr = s.exec_command('ifconfig')
    print(stdout.read())
    s.close()

