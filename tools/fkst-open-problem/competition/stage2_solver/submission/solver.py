#!/usr/bin/env python3
"""Zero-LLM Solo solver for SAIR-EQT2 Stage 2.

The solver reads one startup JSON message from stdin and tries, in order:
a finite-magma counterexample (false branch: brute Fin 2-3, F_p linear p<=7,
F_2^2/Fin 4 matrix-linear, all via finOpTable), then a singleton true proof,
then a substitution-instance (Birkhoff) true proof. Each candidate is verified
by the judge; if none produces a Lean-checkable certificate the solver answers
nothing (no LLM fallback, no fabricated verdict).
"""

import json
import re
import sys
from itertools import product


VAR_ORDER = tuple("abcdefghijklmnopqrstuvwxyz")
# finOpTable only parses single-digit entries correctly.
PRIMES = (2, 3, 5, 7)
AFFINE_PRIMES = (2, 3, 5, 7)
AFFINE_CANDIDATE_LIMIT = 80000
F2_MATRICES_2 = tuple(
    (
        ((bits >> 0) & 1, (bits >> 1) & 1),
        ((bits >> 2) & 1, (bits >> 3) & 1),
    )
    for bits in range(16)
)
F2_ZERO_2 = ((0, 0), (0, 0))
F2_ID_2 = ((1, 0), (0, 1))
F2_VECTORS_2 = ((0, 0), (1, 0), (0, 1), (1, 1))


class ParseError(ValueError):
    pass


def read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


def tokenize(source):
    tokens = []
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
        elif ch in "()=":
            tokens.append(ch)
            i += 1
        elif ch == "\u25c7":
            tokens.append("D")
            i += 1
        elif "a" <= ch <= "z":
            tokens.append(ch)
            i += 1
        else:
            raise ParseError("unexpected character %r" % ch)
    return tokens


class Parser:
    def __init__(self, text):
        self.tokens = tokenize(text)
        self.pos = 0

    def peek(self):
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def take(self, token=None):
        got = self.peek()
        if got is None:
            raise ParseError("unexpected end of input")
        if token is not None and got != token:
            raise ParseError("expected %r, got %r" % (token, got))
        self.pos += 1
        return got

    def parse_equation(self):
        left = self.parse_expr()
        self.take("=")
        right = self.parse_expr()
        if self.peek() is not None:
            raise ParseError("trailing token %r" % self.peek())
        variables = []
        seen = set()
        collect_vars(left, seen, variables)
        collect_vars(right, seen, variables)
        return {"left": left, "right": right, "variables": variables}

    def parse_expr(self):
        left = self.parse_atom()
        while self.peek() == "D":
            self.take("D")
            right = self.parse_atom()
            left = ("op", left, right)
        return left

    def parse_atom(self):
        token = self.peek()
        if token is None:
            raise ParseError("unexpected end of term")
        if token == "(":
            self.take("(")
            term = self.parse_expr()
            self.take(")")
            return term
        if len(token) == 1 and "a" <= token <= "z":
            self.take()
            return ("var", token)
        raise ParseError("unexpected token %r" % token)


def parse_equation(text):
    return Parser(text).parse_equation()


def collect_vars(term, seen, out):
    if term[0] == "var":
        if term[1] not in seen:
            seen.add(term[1])
            out.append(term[1])
        return
    collect_vars(term[1], seen, out)
    collect_vars(term[2], seen, out)


def eval_term(term, env, op):
    if term[0] == "var":
        return env[term[1]]
    return op(eval_term(term[1], env, op), eval_term(term[2], env, op))


def equation_holds(eq, n, op):
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, op) != eval_term(eq["right"], env, op):
            return False
    return True


def equation_fails(eq, n, op):
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, op) != eval_term(eq["right"], env, op):
            return True
    return False


def table_to_op(table):
    return lambda a, b: table[a][b]


def exhaustive_tables(n):
    total = n ** (n * n)
    for enc in range(total):
        x = enc
        table = []
        for _i in range(n):
            row = []
            for _j in range(n):
                row.append(x % n)
                x //= n
            table.append(row)
        yield table


def brute_counterexample(eq1, eq2, max_n=3):
    for n in range(2, max_n + 1):
        for table in exhaustive_tables(n):
            op = table_to_op(table)
            if equation_holds(eq1, n, op) and equation_fails(eq2, n, op):
                return {"stage": "brute", "n": n, "table": table}
    return None


def linear_coeffs(term, p, a, b):
    if term[0] == "var":
        return {term[1]: 1 % p}
    left = linear_coeffs(term[1], p, a, b)
    right = linear_coeffs(term[2], p, a, b)
    out = {}
    for var, coeff in left.items():
        out[var] = (out.get(var, 0) + a * coeff) % p
    for var, coeff in right.items():
        out[var] = (out.get(var, 0) + b * coeff) % p
    return {var: coeff for var, coeff in out.items() if coeff % p}


def coeff_delta(eq, p, a, b):
    left = linear_coeffs(eq["left"], p, a, b)
    right = linear_coeffs(eq["right"], p, a, b)
    variables = set(left) | set(right)
    return {v: (left.get(v, 0) - right.get(v, 0)) % p for v in variables}


def linear_equation_holds(eq, p, a, b):
    return all(value == 0 for value in coeff_delta(eq, p, a, b).values())


def linear_equation_fails(eq, p, a, b):
    return any(value != 0 for value in coeff_delta(eq, p, a, b).values())


def linear_table(p, a, b):
    return [[(a * i + b * j) % p for j in range(p)] for i in range(p)]


def linear_counterexample(eq1, eq2):
    for p in PRIMES:
        for a in range(p):
            for b in range(p):
                if linear_equation_holds(eq1, p, a, b) and linear_equation_fails(eq2, p, a, b):
                    return {"stage": "linear", "n": p, "a": a, "b": b, "table": linear_table(p, a, b)}
    return None


def affine_coeffs(term, p, a, b, c):
    if term[0] == "var":
        return {term[1]: 1 % p}, 0
    left, left_const = affine_coeffs(term[1], p, a, b, c)
    right, right_const = affine_coeffs(term[2], p, a, b, c)
    out = {}
    for var, coeff in left.items():
        out[var] = (out.get(var, 0) + a * coeff) % p
    for var, coeff in right.items():
        out[var] = (out.get(var, 0) + b * coeff) % p
    const = (a * left_const + b * right_const + c) % p
    return {var: coeff for var, coeff in out.items() if coeff % p}, const


def affine_delta(eq, p, a, b, c):
    left, left_const = affine_coeffs(eq["left"], p, a, b, c)
    right, right_const = affine_coeffs(eq["right"], p, a, b, c)
    variables = set(left) | set(right)
    delta = {v: (left.get(v, 0) - right.get(v, 0)) % p for v in variables}
    delta[""] = (left_const - right_const) % p
    return delta


def affine_equation_holds(eq, p, a, b, c):
    return all(value == 0 for value in affine_delta(eq, p, a, b, c).values())


def affine_equation_fails(eq, p, a, b, c):
    return any(value != 0 for value in affine_delta(eq, p, a, b, c).values())


def affine_table(p, a, b, c):
    return [[(a * i + b * j + c) % p for j in range(p)] for i in range(p)]


def affine_counterexample(eq1, eq2):
    tested = 0
    for p in AFFINE_PRIMES:
        for a in range(p):
            for b in range(p):
                if tested >= AFFINE_CANDIDATE_LIMIT:
                    return None
                tested += 1
                # With no constants in the input language, all nonzero affine
                # offsets have the same equational hold/fail behavior.
                c = 1
                if affine_equation_holds(eq1, p, a, b, c) and affine_equation_fails(eq2, p, a, b, c):
                    return {
                        "stage": "affine",
                        "n": p,
                        "a": a,
                        "b": b,
                        "c": c,
                        "table": affine_table(p, a, b, c),
                    }
    return None


def f2_mat_add(x, y):
    return (
        (x[0][0] ^ y[0][0], x[0][1] ^ y[0][1]),
        (x[1][0] ^ y[1][0], x[1][1] ^ y[1][1]),
    )


def f2_mat_mul(x, y):
    return (
        (
            (x[0][0] & y[0][0]) ^ (x[0][1] & y[1][0]),
            (x[0][0] & y[0][1]) ^ (x[0][1] & y[1][1]),
        ),
        (
            (x[1][0] & y[0][0]) ^ (x[1][1] & y[1][0]),
            (x[1][0] & y[0][1]) ^ (x[1][1] & y[1][1]),
        ),
    )


def f2_mat_vec_mul(x, v):
    return (
        (x[0][0] & v[0]) ^ (x[0][1] & v[1]),
        (x[1][0] & v[0]) ^ (x[1][1] & v[1]),
    )


def f2_vec_add(x, y):
    return (x[0] ^ y[0], x[1] ^ y[1])


def f2_matrix_coeffs(term, a, b):
    if term[0] == "var":
        return {term[1]: F2_ID_2}, (0, 0)
    left, left_const = f2_matrix_coeffs(term[1], a, b)
    right, right_const = f2_matrix_coeffs(term[2], a, b)
    out = {}
    for var, coeff in left.items():
        out[var] = f2_mat_add(out.get(var, F2_ZERO_2), f2_mat_mul(a, coeff))
    for var, coeff in right.items():
        out[var] = f2_mat_add(out.get(var, F2_ZERO_2), f2_mat_mul(b, coeff))
    const = f2_vec_add(f2_mat_vec_mul(a, left_const), f2_mat_vec_mul(b, right_const))
    return {var: coeff for var, coeff in out.items() if coeff != F2_ZERO_2}, const


def f2_matrix_affine_coeffs(term, a, b, c):
    coeffs, const = f2_matrix_coeffs(term, a, b)
    if term[0] == "var":
        return coeffs, const
    return coeffs, f2_vec_add(const, c)


def f2_matrix_delta(eq, a, b, c=None):
    coeff_fn = f2_matrix_coeffs if c is None else f2_matrix_affine_coeffs
    if c is None:
        left, left_const = coeff_fn(eq["left"], a, b)
        right, right_const = coeff_fn(eq["right"], a, b)
    else:
        left, left_const = coeff_fn(eq["left"], a, b, c)
        right, right_const = coeff_fn(eq["right"], a, b, c)
    variables = set(left) | set(right)
    delta = {v: f2_mat_add(left.get(v, F2_ZERO_2), right.get(v, F2_ZERO_2)) for v in variables}
    delta[""] = f2_vec_add(left_const, right_const)
    return delta


def f2_matrix_equation_holds(eq, a, b, c=None):
    return all(value == F2_ZERO_2 or value == (0, 0) for value in f2_matrix_delta(eq, a, b, c).values())


def f2_matrix_equation_fails(eq, a, b, c=None):
    return any(value != F2_ZERO_2 and value != (0, 0) for value in f2_matrix_delta(eq, a, b, c).values())


def f2_matrix_counterexample(eq1, eq2, use_affine=True):
    for a in F2_MATRICES_2:
        for b in F2_MATRICES_2:
            if f2_matrix_equation_holds(eq1, a, b) and f2_matrix_equation_fails(eq2, a, b):
                return {"stage": "f2_matrix", "n": 4, "a_mat": a, "b_mat": b}
    if use_affine:
        for a in F2_MATRICES_2:
            for b in F2_MATRICES_2:
                for c in F2_VECTORS_2[1:]:
                    if f2_matrix_equation_holds(eq1, a, b, c) and f2_matrix_equation_fails(eq2, a, b, c):
                        return {"stage": "f2_matrix_affine", "n": 4, "a_mat": a, "b_mat": b, "c_vec": c}
    return None


# affine stage disabled by default: empirically +0 on normal+hard1/2/3 samples
# (with no constants in the input language, nonzero affine offsets are
# equationally equivalent to linear), and it costs up to AFFINE_CANDIDATE_LIMIT
# evals/problem. Kept for reference; flip use_affine=True to re-enable.
def search_counterexample(eq1_text, eq2_text, use_linear=True, use_affine=False):
    eq1 = parse_equation(eq1_text)
    eq2 = parse_equation(eq2_text)
    found = brute_counterexample(eq1, eq2, max_n=3)
    if found is not None:
        return found
    if use_linear:
        found = linear_counterexample(eq1, eq2)
        if found is not None:
            return found
        found = f2_matrix_counterexample(eq1, eq2)
        if found is not None:
            return found
        if use_affine:
            return affine_counterexample(eq1, eq2)
    return None


def make_false_code(problem, cex):
    n = cex["n"]
    if "a" in cex and "b" in cex:
        a, b = cex["a"], cex["b"]
        if "c" in cex:
            table = affine_table(n, a, b, cex["c"])
        else:
            table = linear_table(n, a, b)
        cex = dict(cex)
        cex["table"] = table

    # False certificates must stay within the official declaration whitelist.
    # Linear, affine, brute, and Fin4 matrix witnesses use finOpTable.
    head = (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        # larger carriers overflow decideFin!'s default recursion / heartbeat budget;
        # lift both within the 300s lean_timeout.
        "set_option maxRecDepth 1000000 in\n"
        "set_option maxHeartbeats 1000000 in\n"
        "def submission : Goal := by\n"
    )
    tail = (
        f"  refine \u27e8Fin {n}, m, ?_\u27e9\n"
        f"  decideFin!\n"
    )
    if "a_mat" in cex and "b_mat" in cex:
        a, b = cex["a_mat"], cex["b_mat"]
        c = cex.get("c_vec", (0, 0))
        table = []
        for i in range(4):
            row = []
            for j in range(4):
                lo = (
                    a[0][0] * (i % 2)
                    + a[0][1] * ((i // 2) % 2)
                    + b[0][0] * (j % 2)
                    + b[0][1] * ((j // 2) % 2)
                    + c[0]
                )
                hi = (
                    a[1][0] * (i % 2)
                    + a[1][1] * ((i // 2) % 2)
                    + b[1][0] * (j % 2)
                    + b[1][1] * ((j // 2) % 2)
                    + c[1]
                )
                row.append(((lo % 2) + 2 * (hi % 2)) % 4)
            table.append(row)
        cex = dict(cex)
        cex["table"] = table
    table_str = json.dumps(cex["table"])
    op = (
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        f"  }}\n"
    )
    return head + op + tail


def make_true_code(problem, proof_body):
    lines = proof_body.strip().split("\n")
    indented = "\n".join("  " + l if l.strip() else "" for l in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


def _distinct_vars(text):
    out, seen = [], set()
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def singleton_true_proof(eq1_text, eq2_text):
    # No-LLM proof for true implications whose hypothesis E1 has the form
    # `x = <term not containing x>`: such a law forces the magma to be a singleton
    # (all elements equal), so any E2 follows. Mirrors the official baseline's
    # singleton stage. Returns a proof body string, or None if E1 isn't this shape.
    parts = eq1_text.split("=", 1)
    if len(parts) != 2 or parts[0].strip() != "x":
        return None
    if "x" in set(re.findall(r"\b([a-z])\b", parts[1])):
        return None
    eq1_vars = _distinct_vars(eq1_text)
    eq2_vars = _distinct_vars(eq2_text)
    rhs_lhs, rhs_rhs = eq2_text.split("=", 1)
    filler = " ".join(["a"] * (len(eq1_vars) - 1))
    return (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : ∀ (a b : G), a = b := "
        f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"exact singleton ({rhs_lhs.strip()}) ({rhs_rhs.strip()})"
    )


def _term_to_lean(term):
    if term[0] == "var":
        return term[1]
    return f"({_term_to_lean(term[1])} ◇ {_term_to_lean(term[2])})"


def _match_term(pattern, subject, subst):
    if pattern[0] == "var":
        var = pattern[1]
        if var in subst:
            return subst[var] == subject
        subst[var] = subject
        return True
    if pattern[0] == "op" and subject[0] == "op":
        return _match_term(pattern[1], subject[1], subst) and _match_term(pattern[2], subject[2], subst)
    return False


def _apply_subst(term, subst):
    if term[0] == "var":
        return subst.get(term[1], term)
    return ("op", _apply_subst(term[1], subst), _apply_subst(term[2], subst))


def _count_occurrences(term, needle):
    count = 1 if term == needle else 0
    if term[0] == "op":
        count += _count_occurrences(term[1], needle)
        count += _count_occurrences(term[2], needle)
    return count


def _subst_args(eq1_vars, subst):
    if any(var not in subst for var in eq1_vars):
        return None
    return [_term_to_lean(subst[var]) for var in eq1_vars]


def _proof_lines(eq2_vars, tactic_line):
    lines = []
    if eq2_vars:
        lines.append(f"intro {' '.join(eq2_vars)}")
    lines.append(tactic_line)
    return "\n".join(lines)


def _h_application(args):
    if args:
        return f"h {' '.join(args)}"
    return "h"


def substitution_instance_true_proof(eq1_text, eq2_text):
    try:
        eq1 = parse_equation(eq1_text)
        eq2 = parse_equation(eq2_text)
    except ParseError:
        return None

    eq1_vars = _distinct_vars(eq1_text)
    eq2_vars = _distinct_vars(eq2_text)

    subst = {}
    if _match_term(eq1["left"], eq2["left"], subst) and _match_term(eq1["right"], eq2["right"], subst):
        args = _subst_args(eq1_vars, subst)
        if args is not None:
            return _proof_lines(eq2_vars, f"exact {_h_application(args)}")

    subst = {}
    if _match_term(eq1["right"], eq2["left"], subst) and _match_term(eq1["left"], eq2["right"], subst):
        args = _subst_args(eq1_vars, subst)
        if args is not None:
            return _proof_lines(eq2_vars, f"exact ({_h_application(args)}).symm")

    return None


def main():
    startup = read_message()
    problem = startup["problem"]
    eq1_text, eq2_text = problem["equation1"], problem["equation2"]

    # Stage 1: finite-magma counterexample (false branch).
    found = search_counterexample(eq1_text, eq2_text, use_linear=True)
    if found is not None:
        result = call_judge("false", make_false_code(problem, found))
        if result.get("status") == "accepted":
            return

    # Stage 2: singleton proof (true branch, no LLM) for x = (x-free) hypotheses.
    proof = singleton_true_proof(eq1_text, eq2_text)
    if proof is not None:
        result = call_judge("true", make_true_code(problem, proof))
        if result.get("status") == "accepted":
            return

    proof = substitution_instance_true_proof(eq1_text, eq2_text)
    if proof is not None:
        result = call_judge("true", make_true_code(problem, proof))
        if result.get("status") == "accepted":
            return


if __name__ == "__main__":
    main()
