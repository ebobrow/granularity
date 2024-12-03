# Scenarios:
# - You just had a breakthrough but you have to go so you want to write down just enough that you can remember
# - You are trying to convince yourself that something is true
# - You are trying to convince a seasoned mathematician that something is true
# - You are trying to convince a student that somehting is true
# - You are grading an intro discrete student's homework
# - You are grading a graduate student's homework

import random
from copy import deepcopy

# Each list contains sets of possible first, second, etc. steps
templates = [
    [
        ["x \\in ?a \\cup ?b"],
        ["x \\in ?a \\wedge x \\in ?b"],
        ["x \\in ?a", "x \\in ?b"]
    ],
    [
        ["x \\in ?a \\setminus ?b"],
        [
            "x \\in ?a \\wedge x \\notin ?b",
            "x \\in ?a \\cap ?b ^C",
        ],
        ["x \\in ?a", "x \\notin ?b", "x \\in ?b ^C"]
    ],
    [
        ["?a \\subseteq ?b \\cup ?c"],
        ["?a \\subseteq ?b \\wedge ?a \\subseteq ?c"],
        ["?a \\subseteq ?b", "?a \\subseteq ?c"]
    ],
    [
        ["x \\in ?a \\triangle ?b"],
        [
            "x \\in ?a \\setminus ?b \\vee x \\in ?b \\setminus ?a",
            "(x \\in ?a \\wedge x \\notin ?b ) \\vee (x \\in ?b \\wedge x \\notin ?a )",
        ],
        [
            "x \\notin ?a \\cap ?b",
            "x \\in ?a \\cup ?b",
            "x \\in ?a \\vee x \\in ?b"
        ]
    ],
    [
        [
            "x \\in ?a \\setminus ?b \\setminus ?c \\setminus ?d \\setminus ?e \\setminus ?f \\setminus ?g",
            "x \\in ?a \\setminus ( ?b \\cup ?c ) \\setminus ( ?d \\cup ?e ) \\setminus ( ?f \\cup ?g )"
        ],
        ["x \\in ?a \\wedge (x \\notin ?b \\cup ?c \\cup ?d \\cup ?e \\cup ?f \\cup ?g )"],
        ["x \\in ?a", "x \\notin ?c"]
    ],
    [
        ["x \\in ?a \\setminus ( ?b \\setminus ?c )"],
        ["x \\in ?a \\wedge \\neg (x \\in ?b \\wedge x \\notin ?c )"],
        ["x \\in ?a \\wedge (x \\notin ?b \\vee x \\in ?c )"],
        ["x \\in ?a \\cap ( ?c \\setminus ?b )"]
    ],
    [
        ["x \\in ?a \\setminus ( ?b \\setminus ( ?c \\setminus ?d ))"],
        ["x \\in ?a \\wedge \\neg(x \\in ?b \\wedge\\neg(x \\in ?c \\wedge x \\notin ?d ))"],
        ["x \\in ?a \\wedge (x \\notin ?b \\vee (x \\in ?c \\wedge x \\notin ?d ))"],
        [
            "x \\in ?a",
            "x \\in ?b \\rightarrow (x \\in ?c \\wedge x \\notin ?d )",
            "x \\in ?d \\rightarrow x \\notin ?b"
        ]
    ],
    [["?a \\subset ?b"], ["?a \\neq ?b"]],
    [
        ["?a \\subset ?b"],
        ["\\exists x. x \\notin ?a \\wedge x \\in ?b"],
        ["?b \\setminus ?a \\neq \\emptyset", "| ?b \\setminus ?a | > 0"]
    ],
    [
        ["x \\in ( ?a \\cup ?b ) \\triangle ( ?c \\setminus ?d )"],
        [
            "x \\in ( ?a \\cup ?b ) \\setminus ( ?c \\setminus ?d ) \\vee x \\in ( ?c \\setminus ?d ) \\setminus ( ?a \\cup ?b )",
            "x \\in (( ?a \\cup ?b ) \\setminus ( ?c \\setminus ?d )) \\cup (( ?c \\setminus ?d ) \\setminus ( ?a \\cup ?b ))",
        ],
        ["(x \\in ( ?a \\cup ?b ) \\wedge (x \\notin ?c \\vee x \\in ?d )) \\vee (x \\in ?c \\wedge x \\notin ?a \\cup ?b \\cup ?d )"],
        ["x \\in ?c \\rightarrow x \\in ?d \\vee x \\notin ?a \\cup ?b \\cup ?d"]
    ],
    [
        ["x \\notin ?a \\wedge x \\in ?a \\cup ?b"],
        ["x \\notin ?a \\wedge (x \\in ?a \\vee x \\in ?b )"],
        ["x \\in ?b"]
    ],
    [
        ["?a \\subseteq ?b \\wedge ?a \\subseteq ?c \\wedge ?a \\subseteq ?d"],
        ["?a \\subseteq ?b \\cap ?c \\cap ?d"]
    ],
    [
        ["?b \\subseteq ?a \\wedge ?c \\subseteq ?a \\wedge ?d \\subseteq ?a"],
        ["?b \\cap ?c \\cap ?d \\subseteq ?a"]
    ],
    [
        ["?a \\subseteq ?b \\subseteq ?c"],
        ["?a \\cup X \\subseteq ?b \\cup X \\subseteq ?c \\cup X"],
        ["?a \\cup X \\subseteq ?c \\cup X"],
    ]
]

def dedup(l):
    newlist = []
    for e in l:
        if not e in newlist:
            newlist.append(e)
    return newlist

def plug_template(t, vnames, scramble = False):
    temp_vars = [x for x in t[0][0].split(" ") if x.startswith('?')]
    if scramble:
        random.shuffle(temp_vars)
    d = {}
    for k, v in zip(dedup(temp_vars), vnames):
        if not k in d:
            d[k] = v
    newt = deepcopy(t)
    for i in range(len(newt)):
        for j in range(len(newt[i])):
            newt[i][j] = " ".join(d[x] if x.startswith('?') else x for x in newt[i][j].split(" "))
    return newt

alpha_names = [chr(x + 65) for x in range(26)]
num_names = [f"A_{x}" for x in range(1, 26)]
greek_names = ["\\Chi", "\\Gamma", "\\Delta", "\\Omega", "\\Pi", "\\Psi", "\\Phi", "\\Theta"]

for template in templates:
    print("Problem:")
    print("\\begin{align}")
    for i, step in enumerate(plug_template(template, alpha_names)):
        print("&", random.choice(step))
        if i < len(template)-1:
            print("\\\\")
    print("\\end{align}\n")
