import lark
import z3
import sys

match_num = 0

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
?start: sum
  | sum "?" sum ":" sum -> if

?sum: term
  | sum "+" term        -> add
  | sum "-" term        -> sub
  | sum "||" term       -> or

?term: item
  | term "*"  item      -> mul
  | term "/"  item      -> div
  | term ">>" item      -> shr
  | term "<<" item      -> shl
  | term "&&" item      -> and
  | term "^" item       -> xor

?item: NUMBER           -> num
  | "-" item            -> neg
  | CNAME               -> var
  | "(" start ")"
  | "{" (start "|" )+ start "}" -> match

%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()


def interp(tree, lookup):
    """Evaluate the arithmetic expression.

    Pass a tree as a Lark `Tree` object for the parsed expression. For
    `lookup`, provide a function for mapping variable names to values.
    """

    op = tree.data
    if op in (
        "add",
        "sub",
        "mul",
        "div",
        "shl",
        "shr",
        "and",
        "or",
        "xor",
    ):  # Binary operators.
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == "add":
            return lhs + rhs
        elif op == "sub":
            return lhs - rhs
        elif op == "mul":
            return lhs * rhs
        elif op == "div":
            return lhs / rhs
        elif op == "shl":
            return lhs << rhs
        elif op == "shr":
            return lhs >> rhs
        elif op == "or":
            return lhs | rhs
        elif op == "and":
            return lhs & rhs
        elif op == "xor":
            return lhs ^ rhs
    elif op == "neg":  # Negation.
        sub = interp(tree.children[0], lookup)
        return -sub
    elif op == "num":  # Literal number.
        return int(tree.children[0])
    elif op == "var":  # Variable lookup.
        return lookup(tree.children[0])
    elif op == "if":  # Conditional.
        cond = interp(tree.children[0], lookup)
        true = interp(tree.children[1], lookup)
        false = interp(tree.children[2], lookup)
        return (cond != 0) * true + (cond == 0) * false
    elif op == "match":
        return gen_match(tree.children, lookup)


def gen_match(children, lookup):
    global match_num
    if len(children) > 1:
        cond = lookup(f"hm_{match_num}")
        match_num += 1
        true = interp(children[0], lookup)
        return (cond != 0) * true + (cond == 0) * gen_match(
            children[1:], lookup
        )
    else:
        return interp(children[0], lookup)


next_match_id = 0


def pretty(tree, subst={}, paren=False):
    """Pretty-print a tree, with optional substitutions applied.

    If `paren` is true, then loose-binding expressions are
    parenthesized. We simplify boolean expressions "on the fly."
    """

    # Add parentheses?
    if paren:

        def par(s):
            return "({})".format(s)

    else:

        def par(s):
            return s

    op = tree.data
    if op in ("add", "sub", "mul", "div", "shl", "shr", "and", "or", "xor"):
        lhs = pretty(tree.children[0], subst, True)
        rhs = pretty(tree.children[1], subst, True)
        c = {
            "add": "+",
            "sub": "-",
            "mul": "*",
            "div": "/",
            "shl": "<<",
            "shr": ">>",
            "and": "&&",
            "or": "||",
            "xor": "^",
        }[op]
        return par("{} {} {}".format(lhs, c, rhs))
    elif op == "neg":
        sub = pretty(tree.children[0], subst)
        return "-{}".format(sub, True)
    elif op == "num":
        return tree.children[0]
    elif op == "var":
        name = tree.children[0]
        return str(subst.get(name, name))
    elif op == "if":
        cond = pretty(tree.children[0], subst)
        true = pretty(tree.children[1], subst)
        false = pretty(tree.children[2], subst)
        return par("{} ? {} : {}".format(cond, true, false))
    elif op == "match":
        global next_match_id
        res = pretty_match(tree.children, subst)
        next_match_id += len(tree.children) - 1
        return res


def pretty_match(children, subst):
    global next_match_id
    if "{}".format(subst.get(f"hm_{next_match_id}", None)).isdigit():
        for i in range(len(children) - 1):
            sub = subst.get(f"hm_{next_match_id + i}", None)
            if (
                (sub is not None)
                and (not isinstance(sub, str))
                and (f"{sub}".isdigit())
                and (int(f"{sub}") != 0)
            ):
                return pretty(children[i], subst)
        return pretty(children[-1], subst)

    return "{ " + full_pretty_match(children, subst)


def full_pretty_match(children, subst):
    if len(children) == 1:
        return "{} }}".format(pretty(children[0], subst))
    else:
        return "{} | {}".format(
            pretty(children[0], subst), pretty_match(children[1:], subst)
        )


def run(tree, env):
    """Ordinary expression evaluation.

    `env` is a mapping from variable names to values.
    """

    return interp(tree, lambda n: env[n])


def z3_expr(tree, vars=None):
    """Create a Z3 expression from a tree.

    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width 8. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            return v

    return interp(tree, get_var), vars


def solve(phi):
    """Solve a Z3 expression, returning the model."""

    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


def model_values(model):
    """Get the values out of a Z3 model."""
    return {d.name(): model[d] for d in model.decls()}


def synthesize(tree1, tree2):
    """Given two programs, synthesize the values for holes that make
    them equal.

    `tree1` has no holes. In `tree2`, every variable beginning with the
    letter "h" is considered a hole.
    """

    expr1, vars1 = z3_expr(tree1)
    expr2, vars2 = z3_expr(tree2, vars1)

    # Filter out the variables starting with "h" to get the non-hole
    # variables.
    plain_vars = {
        k: v for k, v in {**vars1, **vars2}.items() if not k.startswith("h")
    }

    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )

    # Solve the constraint.
    return solve(goal)


def ex2(source):
    src1, src2 = source.strip().split("\n")

    parser = lark.Lark(GRAMMAR)
    tree1 = parser.parse(src1)
    tree2 = parser.parse(src2)

    model = synthesize(tree1, tree2)
    print(pretty(tree1))
    print(pretty(tree2, model_values(model)))


if __name__ == "__main__":
    # ex2(sys.stdin.read())
    # sys.stdin.readline().strip()
    with open("minisynth/sketches/s8.txt") as f:
        ex2(f.read())
