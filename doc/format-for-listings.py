#!/usr/bin/python3

import sys, re

substitutes = {
    'lambda': '\\lambda',
    'Rightarrow': '\\Rightarrow',
    'bar': '\\vert',
    'le': '\\leq',
    '≠': '\\neq',
    'λ': '\\lambda',
    '⊓': '\\sqcap',
    '⟦': '\\llbracket',
    '〚': '\\llbracket',
    'lbrakk': '\\llbracket',
    '⟧': '\\rrbracket',
    '〛': '\\rrbracket',
    'rbrakk': '\\rrbracket',
    '⊗': '\\otimes',
    'otimes': '\\otimes',
    '⋅': '\\cdot',
    '·': '\\cdot',
    'cdot': '\\cdot',
    '»': '\\text\\guillemotright',
    'guillemotright': '\\text\\guillemotright',
    '∧': '\\land',
    'times': '\\times',
    'equiv': '\\equiv',
    'qq': '\\mathfrak{q}',
}

def substitute(sym):
    txt = substitutes[sym]
    return "\001\\ensuremath{{{}}}\002".format(txt)

replace_isabelle_regexp = re.compile(r"""\\<([a-zA-Z]+)>""")
def replace(text):
    text = re.sub(replace_isabelle_regexp, (lambda m: substitute(m.group(1))), text)
    text = "".join(substitute(c) if ord(c)>127 else c for c in text)
    return text

infile = sys.argv[1]

with open(infile,'rt') as f:
    for line in f.readlines():
        line = line.rstrip()
        line = replace(line)
        print(line)
        
    
