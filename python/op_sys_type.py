import platform

class OpSysType(object):
    """Determines OS Type using platform module"""
    def __getattr__(self,attr):
        if attr == "osx":
            return "osx"
        elif attr == "rhel":
            return "redhat"
        elif attr == "ubu":
            return "ubuntu"
        elif attr == "debian":
            return "debian"
        elif attr == "fbsd":
            return "FreeBSD"
        elif attr == "sun":
            return "SunOS"
        elif attr == "unknown_linux":
            return "unknown_linux"
        elif attr == "unknown":
            return "unknown"
        else:
            raise AttributeError(attr)

    def linuxType(self):
        """Uses various methods to determine Linux Type"""
        if platform.dist()[0] == self.rhel:
            return self.rhel
        elif platform.dist()[0] == self.debian:
            return self.debian
        elif platform.uname()[1] == self.ubu:
            return self.ubu
        else:
            return self.unknown_linux

    def queryOS(self):
        if platform.system() == "Darwin":
            return self.osx
        elif platform.system() == "Linux":
            return self.linuxType()
        elif platform.system() == self.sun:
            return self.sun
        elif platform.system() == self.fbsd:
            return self.fbsd

def fingerprint():
    type = OpSysType()
    print(type.queryOS())

if __name__ == "__main__":
    fingerprint()



