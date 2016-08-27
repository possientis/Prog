import subprocess
import configparser

"""
A ssh based command dispatch system

"""

def readConfig(file="dispatcher.conf"):
    """Extract IP addresss and commands from config file and returns tuple """

    parser = configparser.ConfigParser()
    parser.read(file)
    machines = parser.items("MACHINES")
    commands = parser.items("COMMANDS")

    return machines, commands


if __name__ == "__main__":

    machines, commands = readConfig()
    print("machines = %s" % machines)
    print("commands = %s" % commands)

    for machine in machines:
        user, ip = machine
        for command in commands:
            name, cmd = command
            ssh = "ssh %s@%s %s" %(user, ip, cmd)
            print(ssh)
            subprocess.call(ssh, shell=True)

    
