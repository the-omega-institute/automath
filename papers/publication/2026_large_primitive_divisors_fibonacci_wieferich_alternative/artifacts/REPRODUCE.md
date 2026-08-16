# Reproducing the finite consistency checks

The verifier uses only the Python standard library and is deterministic. It
completely factors `F_d` for `3 <= d <= 60`, recomputes the rank of apparition
of every prime factor directly, and checks the paper's fibotomic radical,
entropy, Binet-error, primitive-part, and prime-power lifting assertions on
that finite range. The normalized exact-rank ratios are reported for scale;
they are not treated as a finite test of the paper's unspecified `o(1)` term.

Run from the manuscript directory:

```powershell
python artifacts\verify_fibonacci_claims.py --max-rank 60 --prime-limit 200 --u-limit 24 --output artifacts\verification_output.txt
python -m unittest discover -s artifacts -p "test_verify_fibonacci_claims.py"
```

The recorded run used Python 3.10.11 on Windows and completed the verifier in
0.131080 seconds; the five unit tests completed in 0.060 seconds. Runtime is
not a mathematical claim and will vary by machine.

The unit test `test_product_constant_perturbation_is_rejected` replaces the
paper's product constant `2/3` by `0.76`. At rank 4 the product margin becomes
`-0.013245226750`, and the verifier raises `AssertionError`. The test then
restores `2/3` and reruns the check successfully. This red-then-green check
establishes that the inequality check can fail when its constant is wrong.

The stored report is `verification_output.txt`. Verify the artifact manifest
from the manuscript directory with:

```powershell
Push-Location artifacts
sha256sum -c SHA256SUMS
Pop-Location
```

`SHA256SUMS` and every artifact it covers use LF line endings.
