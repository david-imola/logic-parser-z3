import sys
from z3 import (And, Bool, BoolRef, BoolVal,
                Implies, Not, Or, Solver, is_true, sat)

# Recursive Rules: X = X&X
#        X = X|X
#        X = X->X
#        X = X<->X
#        X = (X)
#        X = ~X
# Terminal Rules:
#       X = v (where v is a variable)
#       X = T (True)
#       X = F (False)


# z3 variables that get created
VARS = {}


# Used to determine if a function is returning a valid expression,
# or the False boolean
def is_z3(what):
    return isinstance(what, BoolRef)


# X = (X)
def paren(stmt: str, l: int, r: int):
    if stmt[l] == "(" and stmt[r] == ")":
        x = X(stmt, l + 1, r - 1)
        return x if is_z3(x) else False
    return False


# X = v and X = T and X = F
def var(stmt: str, l: int, r: int):
    if r != l:
        return False
    char = stmt[r]
    if char.islower():  # X = variable
        if char not in VARS:
            VARS[char] = Bool(char)
        return VARS[char]
    if char == "T":
        return BoolVal(True)
    if char == "F":
        return BoolVal(False)
    return False


# X = ~X
def negate(stmt: str, l: int, r: int):
    if stmt[l] == "~":
        x = X(stmt, l + 1, r)
        return Not(x) if is_z3(x) else False
    else:
        return False


# Used for the rules that have join two X's
def joint(stmt: str, joiner: str, l: int, r: int):
    length = len(joiner)

    i = stmt.rfind(joiner, l, r+1)
    while i != -1:
        x = X(stmt, l, i - 1)
        y = X(stmt, i + length, r)
        if is_z3(x) and is_z3(y):
            return (x, y)
        i = stmt.rfind(joiner, l, i-1)
    return False


# X = X|X
def disj(stmt: str, l: int, r: int):
    j = joint(stmt, "|", l, r)
    return Or(j[0], j[1]) if j else False


# X = X&X
def conj(stmt: str, l: int, r: int):
    j = joint(stmt, "&", l, r)
    return And(j[0], j[1]) if j else False


# X = X->X
def implies(stmt: str, l: int, r: int):
    j = joint(stmt, "->", l, r)
    return Implies(j[0], j[1]) if j else False


# X = X<->X
def iff(stmt: str, l: int, r: int):
    j = joint(stmt, "<->", l, r)
    return And(Implies(j[0], j[1]), Implies(j[1], j[0])) if j else False


def X(stmt: str, l: int, r: int):

    if l > r:
        return False

    x = paren(stmt, l, r)
    if is_z3(x):
        return x

    x = var(stmt, l, r)
    if is_z3(x):
        return x

    x = iff(stmt, l, r)
    if is_z3(x):
        return x

    x = implies(stmt, l, r)
    if is_z3(x):
        return x

    x = disj(stmt, l, r)
    if is_z3(x):
        return x

    x = conj(stmt, l, r)
    if is_z3(x):
        return x

    x = negate(stmt, l, r)
    if is_z3(x):
        return x

    return False


# Returns valid Z3 expression if the statement gramitcally correct,
# false othersie
def get_z3_expr(text):
    # Remove any whitespace to make things easier
    statement = text.replace(" ", "")
    return X(statement, 0, len(statement) - 1)


# Returns 'T' if true, 'F' if false
def bool_chr(b: bool):
    return "T" if b else "F"


# Prints out the result of testing all possible boolean values
# for the supplied variables.
def test(expr, exprstr):
    s = Solver()
    s.add(expr)
    var_list = sorted(VARS.items())
    top = " | ".join([key for key, _ in var_list]) + " | " + exprstr
    print(top)
    print("=" * len(top))

    # Perumutates by assigning each variable to a bit,
    # Then adds goes from 000->111 (000, 001, 010, 011)
    var_cnt = len(var_list)
    n = 2 ** var_cnt
    for i in range(n):
        ands = []
        boolval = []
        for vi in range(var_cnt):
            bit = 2**(var_cnt - vi - 1)
            istrue = i & bit == bit
            boolval.append(istrue)
            ands.append(And(var_list[vi][1] == True if istrue
                            else var_list[vi][1] == False))
        final = s.check(*ands) == sat
        out = " | ".join([bool_chr(b) for b in boolval])
        out += " | " + bool_chr(final)
        print(out)


def main():
    if len(sys.argv) < 2:
        print("Error: no argument supplied.")
        return 1
    if len(sys.argv) > 2:
        print("Error: Only one argument should be supplied."
              " Note the argument should be surrounded by quotes")
        return 1

    expr = get_z3_expr(sys.argv[1])
    if is_z3(expr):
        test(expr, sys.argv[1])
    else:
        print("Error parsing the supplied argument")
        return 1
    return 0


if __name__ == "__main__":
    main()
