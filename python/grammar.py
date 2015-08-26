grammar = {'<start>':[['This','<object>','is here']],
'<object>':[['computer'],['car'],['assignment']]};


def expand(symbol):
    if symbol.startswith('<'):
        definitions = grammar[symbol]
        expansion = choice(definitions)
        map(expand, expansion)
    else:
        sys.stdout.write(symbol)

expand('<start>')

