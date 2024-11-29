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
        [
            "x \\in ?a \\wedge x \\in ?b",
            "x \\in ?b \\wedge x \\in ?a",
        ],
        ["x \\in ?a", "x \\in ?b"]
    ],
    [["?a \\cup ?b \\cup ?c \\cup ?d"], ["?c \\cup ?a \\cup ?b \\cup ?d"]],
    [
        ["x \\in ?a \\setminus ?b"],
        [
            "x \\in ?a \\wedge x \\notin ?b",
            "x \\notin ?b \\wedge x \\in ?a",
            "x \\in ?a \\cap ?b ^C",
            "x \\in ?b ^C \\cap ?a"
        ],
        [
            "x \\in ?a",
            "x \\notin ?b",
            "x \\in ?b ^C"
        ]
    ],
    [
        ["?a \\subseteq ?b \\cup ?c", "?b \\cup ?c \\supseteq ?a"],
        [
            "?a \\subseteq ?b \\wedge ?a \\subseteq ?c",
            "?a \\subseteq ?c \\wedge ?a \\subseteq ?b",
            "?b \\supseteq ?a \\wedge ?c \\supseteq ?a",
            "?c \\supseteq ?a \\wedge ?b \\supseteq ?a",
        ],
        [
            "?a \\subseteq ?b",
            "?a \\subseteq ?c",
            "?b \\supseteq ?a",
            "?c \\supseteq ?a",
        ]
    ],
    [
        ["x \\in ?a \\triangle ?b"],
        [
            "x \\in ?a \\setminus ?b \\vee x \\in ?b \\setminus ?a",
            "(x \\in ?a \\wedge x \\notin ?b ) \\vee (x \\in ?b \\wedge x \\notin ?a )",
            "(x \\in ?a \\wedge x \\notin ?b ) \\vee (x \\notin ?a \\wedge x \\in ?b )",
            "(x \\notin ?b \\wedge x \\in ?a ) \\vee (x \\notin ?a \\wedge x \\in ?b )",
        ]
    ],
    [
        [
            "x \\in ?a \\setminus ?b \\setminus ?c \\setminus ?d \\setminus ?e \\setminus ?f \\setminus ?g",
            "x \\in ?a \\setminus ( ?b \\cup ?c ) \\setminus ( ?d \\cup ?e ) \\setminus ( ?f \\cup ?g )"
        ],
        [
            "x \\in ?a \\wedge (x \\notin ?b \\cup ?c \\cup ?d \\cup ?e \\cup ?f \\cup ?g )",
            "x \\in ?a \\wedge (x \\notin ?b \\cup ?c \\cup ?d ) \\wedge (x \\notin ?e \\cup ?f \\cup ?g )",
            "x \\in ?a \\wedge (x \\notin ?b \\cup ?d \\cup ?f ) \\wedge (x \\notin ?c \\cup ?e \\cup ?g )",
        ],
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
        [
            "x \\in ?a \\wedge \\neg(x \\in ?b \\wedge\\neg(x \\in ?c \\wedge x \\notin ?d ))",
        ],
        [
            "x \\in ?a \\wedge (x \\notin ?b \\vee (x \\in ?c \\wedge x \\notin ?d ))",
        ],
        [
            "x \\in ?a",
            "x \\in ?b \\rightarrow (x \\in ?c \\wedge x \\notin ?d )",
            "x \\in ?d \\rightarrow x \\notin ?b"
        ]
    ],
    [
        [
            "?a \\subseteq ?b \\subseteq ?c",
            "?c \\supseteq ?b \\supseteq ?a"
        ],
        ["?a \\subseteq ?b", "?a \\subseteq ?c", "?c \\supseteq ?b", "?c \\supseteq ?a"]
    ],
    [["?a \\subset ?b"], ["?a \\neq ?b", "?b \\neq ?a"]],
    [
        ["?a \\subset ?b"],
        [
            "\\exists x. x \\notin ?a \\wedge x \\in ?b",
            "\\exists x. x \\in ?b \\wedge x \\notin ?a",
        ],
        ["?b \\setminus ?a \\neq \\emptyset", "| ?b \\setminus ?a | > 0"]
    ],
    [
        ["(( ?a \\cup ?b ) \\cup ( ?c \\cup ?d \\cup ?e )) \\cup ?f"],
        [
            "?e \\cup ?f \\cup ?c \\cup ?a \\cup ?d \\cup ?b",
            "( ?e \\cup ?f \\cup ?c ) \\cup ?a \\cup ( ?d \\cup ?b )",
        ]
    ]
]

def plug_template_alpha(t, scramble = False):
    temp_vars = [x for x in t[0][0].split(" ") if x.startswith('?')]
    if scramble:
        random.shuffle(temp_vars)
    d = {}
    for k, v in zip(temp_vars, [chr(x + 65) for x in range(26)]):
        if not k in d:
            d[k] = v
    newt = deepcopy(t)
    for i in range(len(newt)):
        for j in range(len(newt[i])):
            newt[i][j] = " ".join(d[x] if x.startswith('?') else x for x in newt[i][j].split(" "))
    return newt

def plug_template_num(t, scramble = False):
    temp_vars = [x for x in t[0][0].split(" ") if x.startswith('?')]
    if scramble:
        random.shuffle(temp_vars)
    d = {}
    for k, v in zip(temp_vars, [f"A_{x}" for x in range(1, 26)]):
        if not k in d:
            d[k] = v
    newt = deepcopy(t)
    for i in range(len(newt)):
        for j in range(len(newt[i])):
            newt[i][j] = " ".join(d[x] if x.startswith('?') else x for x in newt[i][j].split(" "))
    return newt

def plug_template_greek(t, scramble = True):
    temp_vars = [x for x in t[0][0].split(" ") if x.startswith('?')]
    if scramble:
        random.shuffle(temp_vars)
    letters = ["\\Chi", "\\Gamma", "\\Delta", "\\Omega", "\\Pi", "\\Psi", "\\Phi", "\\Theta"]
    d = {}
    for k, v in zip(temp_vars, letters):
        if not k in d:
            d[k] = v
    newt = deepcopy(t)
    for i in range(len(newt)):
        for j in range(len(newt[i])):
            newt[i][j] = " ".join(d[x] if x.startswith('?') else x for x in newt[i][j].split(" "))
    return newt

def pick_steps(t):
    steps = []
    for step in t:
        steps.append(random.choice(step))
    return steps

# print(plug_template_alpha(templates[0]))
# print(plug_template_num(templates[0]))
# print(plug_template_greek(templates[0]))
for template in templates:
    print("Problem:")
    print("\\begin{align}")
    for i, step in enumerate(plug_template_num(template)):
        print("&", random.choice(step))
        if i < len(template)-1:
            print("\\\\")
    print("\\end{align}\n")
