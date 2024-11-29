fof(subset,axiom,
    ! [A, B] : subset(A,B) => (! [X] : in(x, A) => in(X, B))).
fof(union,axiom,
    ! [A, B, X] : in(X,union(A, B)) => (in(X, A) | in(X, B))).

fof(test,conjecture,
    ! [X, A, B, C] : subset(A,B) => subset(union(A,C),union(B,C))).
