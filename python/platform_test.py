import platform

profile = [
        platform.architecture(),
        platform.dist(),
        platform.libc_ver(),
        platform.mac_ver(),
        platform.machine(),
        platform.node(),
        platform.platform(),
        platform.processor(),
        platform.python_build(),
        platform.python_compiler(),
        platform.python_version(),
        platform.system(),
        platform.uname(),
        platform.version(), # this final comma is not a problem it seems
        ]

for item in profile:
    print(item)

