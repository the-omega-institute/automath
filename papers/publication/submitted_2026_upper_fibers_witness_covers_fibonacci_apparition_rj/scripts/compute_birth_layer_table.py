#!/usr/bin/env python3
"""Compute birth layer data for the Fibonacci order-of-apparition map.

Generates LaTeX table for the paper.
Output: generated/tab_birth_layer_data.tex
"""

import os
import math
import time

def fibonacci(n):
    """Compute F_n exactly."""
    if n <= 0:
        return 0
    a, b = 0, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return b

def fib_mod(n, m):
    """Compute F_n mod m."""
    if m == 1:
        return 0
    if n <= 0:
        return 0
    a, b = 0, 1
    for _ in range(n - 1):
        a, b = b, (a + b) % m
    return b % m

def factorize(n):
    """Return sorted list of (prime, exponent) pairs."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1
    if n > 1:
        factors.append((n, 1))
    return factors

def get_divisors(n):
    """Return sorted list of all positive divisors of n."""
    if n <= 0:
        return []
    if n == 1:
        return [1]
    factors = factorize(n)
    divs = [1]
    for p, e in factors:
        new_divs = []
        for d in divs:
            pe = 1
            for _ in range(e + 1):
                new_divs.append(d * pe)
                pe *= p
        divs = new_divs
    return sorted(divs)

def omega(n):
    """Number of distinct prime factors of n."""
    if n <= 1:
        return 0
    return len(factorize(n))

def alpha_for_Fn_divisor(q, n):
    """Given that q | F_n, compute alpha(q) = min d | n with q | F_d."""
    if q == 1:
        return 1
    divs_n = sorted(get_divisors(n))
    for d in divs_n:
        if d >= 1 and fib_mod(d, q) == 0:
            return d
    return n

def compute_birth_layer(n):
    """Compute B_n and M_n for the birth layer at index n."""
    Fn = fibonacci(n)
    if Fn <= 1:
        return Fn, [], []

    divs_Fn = get_divisors(Fn)
    B_n = []
    for q in divs_Fn:
        if q >= 2 and alpha_for_Fn_divisor(q, n) == n:
            B_n.append(q)

    # Compute minimal generators
    M_n = []
    for m in sorted(B_n):
        is_minimal = True
        for d in M_n:
            if m % d == 0 and d != m:
                is_minimal = False
                break
        if is_minimal:
            M_n.append(m)

    return Fn, B_n, M_n

def factorization_str(n):
    """LaTeX string for the factorization of n."""
    if n <= 1:
        return str(n)
    factors = factorize(n)
    parts = []
    for p, e in factors:
        if e == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{{{e}}}")
    return " \\cdot ".join(parts)

def main():
    n_max = 30
    print(f"Computing birth layer data for n = 2..{n_max}")
    print()

    results = []
    t0 = time.time()

    for n in range(2, n_max + 1):
        Fn, B_n, M_n = compute_birth_layer(n)
        A_n = len(B_n)
        M_n_count = len(M_n)
        om_n = omega(n)

        M_n_display = M_n[:6]
        M_n_str = ", ".join(str(m) for m in M_n_display)
        if len(M_n) > 6:
            M_n_str += ", ..."

        results.append({
            'n': n, 'omega': om_n, 'Fn': Fn,
            'A': A_n, 'M_count': M_n_count, 'M': M_n
        })

        elapsed = time.time() - t0
        print(f"  n={n:>2}: F_n={Fn}, omega(n)={om_n}, "
              f"A(n)={A_n:>4}, #M_n={M_n_count:>3}, "
              f"M_n={{{M_n_str}}}  [{elapsed:.1f}s]")

    # Generate LaTeX table
    outdir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                          "generated")
    os.makedirs(outdir, exist_ok=True)
    outpath = os.path.join(outdir, "tab_birth_layer_data.tex")

    lines = []
    lines.append("\\begin{table}[ht]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\caption{Birth layer data for $2 \\le n \\le 30$. "
                 "Here $\\omega(n)$ is the number of distinct prime divisors of $n$, "
                 "$A(n)=\\#B_n$ is the birth layer cardinality, and "
                 "$\\#\\mathcal{M}_n$ is the number of minimal generators.}")
    lines.append("\\label{tab:birth-layer-data}")
    lines.append("\\begin{tabular}{rrcrr}")
    lines.append("\\toprule")
    lines.append("$n$ & $\\omega(n)$ & $F_n$ & $A(n)$ & $\\#\\mathcal{M}_n$ \\\\")
    lines.append("\\midrule")

    for r in results:
        n = r['n']
        Fn = r['Fn']
        if Fn > 10**7:
            Fn_str = factorization_str(Fn)
        else:
            Fn_str = f"{Fn}"
            factors = factorize(Fn)
            if len(factors) > 1 or (len(factors) == 1 and factors[0][1] > 1):
                Fn_str += f" = {factorization_str(Fn)}"

        lines.append(f"  {n} & {r['omega']} & ${Fn_str}$ & {r['A']} & {r['M_count']} \\\\")

    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    tex_content = "\n".join(lines)
    with open(outpath, "w", encoding="utf-8") as f:
        f.write(tex_content)

    print(f"\nLaTeX table written to: {outpath}")
    print(f"\nTotal time: {time.time() - t0:.1f}s")

    # Also print minimal generator details for key cases
    print("\n--- Minimal generator details ---")
    for r in results:
        n = r['n']
        if r['M_count'] > 1 or r['omega'] >= 2:
            M_str = ", ".join(str(m) for m in r['M'][:10])
            if len(r['M']) > 10:
                M_str += ", ..."
            print(f"  n={n}: M_n = {{{M_str}}}")

if __name__ == "__main__":
    main()
