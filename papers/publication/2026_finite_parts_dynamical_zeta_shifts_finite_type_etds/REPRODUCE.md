# Reproducing the exact S3 certificate

The manuscript prints a self-contained rational proof of the interval for
`F_epsilon(1/2)`. The program below independently reproduces the logarithm
brackets, rational tails, and final comparisons.

## Permanent source

Repository:

https://github.com/the-omega-institute/automath

Content-addressed program URL:

https://github.com/the-omega-institute/automath/blob/27d7e8fa74de6860723b81cd5cc3b01139909be7/papers/publication/2026_finite_parts_dynamical_zeta_shifts_finite_type_etds/certificates/s3_log_certificates.py

Program SHA-256:

```text
301737D892108D115F6F70128D03EBF6291F9E91D5811306E7D8A49F915D510C
```

## Environment

- Python 3.11 or later
- SymPy 1.13.1
- Run commands from the manuscript directory

Install the only non-standard dependency:

```powershell
python -m pip install "sympy==1.13.1"
```

## Verification

Run:

```powershell
python certificates/s3_log_certificates.py
```

The program exits with status zero and ends with:

```text
fixed-label windows verified
```

To regenerate the stored plain-text certificate:

```powershell
python certificates/s3_log_certificates.py --write-cert certificates/s3_log_certificates.cert
```

The calculation uses exact rational arithmetic. No floating-point root or
logarithm approximation is used as certificate evidence.

## Boundary collision, minimality, quotient, harmonic, and Fourier checks

The additional exact verification enumerates primitive binary necklaces in a
strict-gap `C2` extension, compares the quotient split-orbit correction with
the periodic-minus-fixed power series through degree 16, derives the universal
harmonic jet symbolically, and checks the exact four-vertex boundary collision.
It also verifies a positive rational Mahler certificate on a real parameter
grid and an exact counterexample showing that positivity cannot be omitted
from the rational-certificate kernel domain.  A diagonal signed-block model
checks that the remaining special-value interface occurs within the same-base
compatibility and strict-gap constraints.
It also exhausts all `10^4` four-vertex two-out-regular base matrices and every
compatible signed block used in the polynomial-certificate minimality proof.
The same exact-arithmetic program executes the finite rational Mahler
coefficient recursion and Pade system on accepted and rejected inputs, checks
the cleared polynomial identity, and verifies the stated degree, height, and
same-base determinant coefficient bounds.
It reconstructs the four-vertex collision certificate
\(R=1-z+4z^2\), isolates \(1/4\) as its only collision radius in
\(0<z\le1/4\), checks the theorem's \(N-1=959\) collision bound, and records
the corresponding \(N_*=960\) algebraic-sample recovery budget.
It also audits the exact specialization of Nishioka's 1982 theorem used in
Theorem 6.8: `p=2`, `N=0`, `n=1`, `m=M=2`, `U=L=1`, coprimality of the
reduced equation, and the numerical inequality `4<8`.  This is parameter
bookkeeping; the published transcendence theorem remains an external analytic
input and is not claimed to be machine-verified.
The expected enumeration is `2208` primitive bases, `48` supports for
`1-z^2+2z^4`, and `0` supports for `(1-z+2z^2)^2`.  A separate high-precision
check evaluates the telescoping identity at 25 points in `0 < z <= 1/4`:

```powershell
python -m unittest artifacts.test_verify_a5_results -v
python artifacts/verify_a5_results.py
```

The second command exits with status zero and ends with:

```text
STATUS: PASS
```
