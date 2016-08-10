import paramiko
import os

hostname = '192.168.1.xxx'
port = 22
username = 'xxx'
password = 'xxx'
dir_path = '/home/xxx'



if __name__ == "__main__":
    t = paramiko.Transport((hostname, port))
    t.connect(username=username, password=password)
    sftp = paramiko.SFTPClient.from_transport(t)
    files = sftp.listdir(dir_path) 
    print(files)
    print('Retrieving log1')
    sftp.get(os.path.join(dir_path,'log1'), './log1')
    print('Retrieving log2')
    sftp.get(os.path.join(dir_path,'log2'), './log2')


    t.close()

