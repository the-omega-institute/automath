#!/usr/bin/env python3
"""Pure-Python verifier for finite magma counterexamples."""

import argparse
import json
from itertools import product


class ParseError(ValueError):
    pass


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


def collect_vars(term, seen, out):
    if term[0] == "var":
        if term[1] not in seen:
            seen.add(term[1])
            out.append(term[1])
        return
    collect_vars(term[1], seen, out)
    collect_vars(term[2], seen, out)


def parse_equation(text):
    return Parser(text).parse_equation()


def valid_table(table):
    if not isinstance(table, list) or not table:
        return False
    n = len(table)
    for row in table:
        if not isinstance(row, list) or len(row) != n:
            return False
        for value in row:
            if not isinstance(value, int) or value < 0 or value >= n:
                return False
    return True


def eval_term(term, env, table):
    if term[0] == "var":
        return env[term[1]]
    left = eval_term(term[1], env, table)
    right = eval_term(term[2], env, table)
    return table[left][right]


def equation_holds(eq, table):
    n = len(table)
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, table) != eval_term(eq["right"], env, table):
            return False
    return True


def equation_fails(eq, table):
    n = len(table)
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, table) != eval_term(eq["right"], env, table):
            return True
    return False


def verify_counterexample(equation1, equation2, table):
    if not valid_table(table):
        return False
    eq1 = parse_equation(equation1)
    eq2 = parse_equation(equation2)
    return equation_holds(eq1, table) and equation_fails(eq2, table)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("equation1")
    parser.add_argument("equation2")
    parser.add_argument("table_json")
    args = parser.parse_args()
    table = json.loads(args.table_json)
    print("PASS" if verify_counterexample(args.equation1, args.equation2, table) else "FAIL")


if __name__ == "__main__":
    main()
