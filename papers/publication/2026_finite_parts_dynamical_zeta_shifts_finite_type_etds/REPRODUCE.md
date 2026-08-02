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
