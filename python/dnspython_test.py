import dns.resolver

ip = dns.resolver.query("oreilly.com", "A")
mail = dns.resolver.query("oreilly.com", "MX")

print(ip.response)
print(list(ip))

print(mail.response)
print(list(mail))
