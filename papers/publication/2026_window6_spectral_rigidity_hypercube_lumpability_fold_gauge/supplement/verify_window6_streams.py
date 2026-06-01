#!/usr/bin/env python3
"""Pure-Python verifier for canonical non-Sage window-6 audit streams.

Run from the paper root:
    python supplement/verify_window6_streams.py

This verifies the printed fiber streams, directed edge-count stream,
geometric stabilizer stream, and residual witness stream.  The exact
characteristic polynomial and Sturm interval checks are verified by the
Sage script window6_audit_certificate.sage.
"""
from hashlib import sha256
from fractions import Fraction
from itertools import product
from pathlib import Path
import sys

EXPECTED = {
    "fiber_m6": "3b3a9f44074afc02177af79f9f4107aea061789f817bf7d288cb9fd473cdeee5",
    "fiber_m7": "4a182c2503f6a82433ed6501cdea0997d5d274ef7b35415e3b0ec0d2cb7e7232",
    "fiber_m8": "cce73204f542296c6966285ca60f307f97a630814b9fd108c85cd3b974351c36",
    "edge_matrix_m6": "2bbf7acda82a4c07d39ac76a621cee9751abaf253f6298d8540704146a2db4f0",
    "stabilizer_m6": "74c06d9b2d8cf118170272b1f9320782f73d4e82d940061dcd37f85b7d1f87bf",
    "residual_witness_m6": "701cfebf8b51ad99e38663841599aa1b1a492957040c4db6d4dd3e2def69fcf2",
    "stochastic_budget_m6": "262acb15abd5a39641695a889c156019d5a197b491ce0e28c103f8b67c154f63",
}

FIB = [0, 1]
while len(FIB) < 200:
    FIB.append(FIB[-1] + FIB[-2])

def legal(m):
    return ["".join(bits) for bits in product("01", repeat=m) if "11" not in "".join(bits)]

def zprefix(N, m):
    z = [0] * 200
    r = N
    while r > 0:
        j = max(i for i in range(1, 150) if FIB[i + 1] <= r)
        z[j - 1] = 1
        r -= FIB[j + 1]
    return "".join(str(a) for a in z[:m])

def audit(m):
    X = legal(m)
    d = {x: 0 for x in X}
    for N in range(2 ** m):
        d[zprefix(N, m)] += 1
    bd = [x for x in X if x[0] == "1" and x[-1] == "1"]
    dv = [d[x] for x in X]
    return "m=%d;X=%s;d=%s;bd=%s" % (
        m,
        ",".join(X),
        ",".join(map(str, dv)),
        ",".join("%s:%d" % (x, d[x]) for x in bd),
    )

def edge_stream_m6():
    X = legal(6)
    pos = {x: i for i, x in enumerate(X)}
    d = [0 for _ in X]
    for N in range(2 ** 6):
        d[pos[zprefix(N, 6)]] += 1
    Nmat = [[0 for _ in X] for _ in X]
    for a in product([0, 1], repeat=6):
        s = "".join(map(str, a))
        i = pos[zprefix(int(s, 2), 6)]
        for k in range(6):
            b = list(a)
            b[k] = 1 - b[k]
            t = "".join(map(str, b))
            j = pos[zprefix(int(t, 2), 6)]
            Nmat[i][j] += 1
    rows = [
        "%d:%s" % (i, ",".join("%d:%d" % (j, c) for j, c in enumerate(row) if c))
        for i, row in enumerate(Nmat)
    ]
    return "m=6;states=%s;d=%s;N=%s" % (
        ",".join(X), ",".join(map(str, d)), ";".join(rows)
    )

def sigma_geo(s):
    a = [int(c) for c in s]
    return "".join(map(str, [1 - a[4], a[1], a[2], a[3], 1 - a[0], a[5]]))

def stabilizer_stream_m6():
    pairs = []
    for a in product("01", repeat=6):
        s = "".join(a)
        pairs.append("%s>%s:%s" % (s, sigma_geo(s), zprefix(int(s, 2), 6)))
    return "m=6;sigma_geo=[1-a5,a2,a3,a4,1-a1,a6];pairs=" + ";".join(pairs)

def residual_stream_m6():
    def neighbor_count(source, target):
        N = int(source, 2)
        return sum(1 for k in range(6) if zprefix(N ^ (1 << (5 - k)), 6) == target)
    return "m=6;residual=000000,010101->000100;folds=%s,%s;counts=%s,%s" % (
        zprefix(int("000000", 2), 6),
        zprefix(int("010101", 2), 6),
        neighbor_count("000000", "000100"),
        neighbor_count("010101", "000100"),
    )


def frac_text(value):
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"

def stochastic_budget_stream_m6():
    m = 6
    X = legal(m)
    fibers = {x: [] for x in X}
    for bits in product("01", repeat=m):
        source = "".join(bits)
        fibers[zprefix(int(source, 2), m)].append(source)

    counts = {}
    for source in ("".join(bits) for bits in product("01", repeat=m)):
        source_value = int(source, 2)
        counts[source] = {
            target: sum(
                1 for k in range(m)
                if zprefix(source_value ^ (1 << (m - 1 - k)), m) == target
            )
            for target in X
        }

    def row_data(epsilon):
        data = {}
        for x in X:
            lower_sum = Fraction(0)
            upper_sum = Fraction(0)
            max_diameter = 0
            for y in X:
                values = [counts[source][y] for source in fibers[x]]
                low = Fraction(min(values), m)
                high = Fraction(max(values), m)
                max_diameter = max(max_diameter, max(values) - min(values))
                lower_sum += max(Fraction(0), high - epsilon)
                upper_sum += min(Fraction(1), low + epsilon)
            data[x] = (max_diameter, lower_sum, upper_sum)
        return data

    data_0 = row_data(Fraction(0))
    data_12 = row_data(Fraction(1, 12))
    data_6 = row_data(Fraction(1, 6))
    rows_0 = [x for x in X if data_0[x][0] == 0]
    rows_12 = [x for x in X if data_0[x][0] == 1]
    rows_6 = [x for x in X if data_0[x][0] == 2]

    def lu(rows, data):
        return ";".join(
            "%s:%s,%s" % (x, frac_text(data[x][1]), frac_text(data[x][2]))
            for x in rows
        )

    return (
        "m=6;stochastic_budget;rho=1/6;"
        "rows=0:%s|1/12:%s;LU=%s|1/6:%s;LU=%s" % (
            ",".join(rows_0),
            ",".join(rows_12),
            lu(rows_12, data_12),
            ",".join(rows_6),
            lu(rows_6, data_6),
        )
    )

GENERATED = {
    "fiber_m6": audit(6),
    "fiber_m7": audit(7),
    "fiber_m8": audit(8),
    "edge_matrix_m6": edge_stream_m6(),
    "stabilizer_m6": stabilizer_stream_m6(),
    "residual_witness_m6": residual_stream_m6(),
    "stochastic_budget_m6": stochastic_budget_stream_m6(),
}

def parse_stream_file(path):
    found = {}
    current = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("[") and line.endswith("]"):
            current = line[1:-1]
            found[current] = {"sha256": None, "stream": None}
        elif current and line.startswith("sha256="):
            found[current]["sha256"] = line.split("=", 1)[1]
        elif current and line:
            found[current]["stream"] = line
    return found

def main():
    errors = []
    for name, stream in GENERATED.items():
        digest = sha256(stream.encode()).hexdigest()
        if digest != EXPECTED[name]:
            errors.append(f"generated {name} hash {digest} != expected {EXPECTED[name]}")
    stream_path = Path(__file__).with_name("window6_canonical_streams.txt")
    printed = parse_stream_file(stream_path)
    for name, expected_hash in EXPECTED.items():
        entry = printed.get(name)
        if entry is None:
            errors.append(f"missing stream block {name}")
            continue
        if entry["sha256"] != expected_hash:
            errors.append(f"printed {name} sha256 {entry['sha256']} != expected {expected_hash}")
        if entry["stream"] != GENERATED[name]:
            errors.append(f"printed {name} stream differs from generated stream")
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("window6 canonical streams: all assertions passed")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
