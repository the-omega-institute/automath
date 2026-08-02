# Reproducing the finite certificates

The mathematical correction theorem is proved in the manuscript. The scripts
below reproduce the exact arithmetic used for the displayed \(S_3\) interval
and the presentation-relative determinant-fibre enumeration.

## Environment

- Python 3.11 or later
- SymPy 1.13.1
- Run commands from this directory

Install the only non-standard dependency:

~~~powershell
python -m pip install "sympy==1.13.1"
~~~

## One-command reproduction

Run both certificate programs and require their success markers:

~~~powershell
python certificates/s3_log_certificates.py; if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }; python artifacts/verify_twisted_determinant_rigidity.py | Tee-Object -Variable verifierOutput; if ($LASTEXITCODE -ne 0 -or $verifierOutput[-1] -ne "STATUS: PASS") { exit 1 }
~~~

The \(S_3\) program ends with:

~~~text
fixed-label windows verified.
~~~

The determinant-fibre verifier ends with:

~~~text
STATUS: PASS
~~~

Its complete expected output is stored in
artifacts/verify_twisted_determinant_rigidity_output.txt.

## Archived revision and integrity

The verifier is present in repository revision:

~~~text
0ee48dc3905b8e44d872d14db84457b614e87ef4
~~~

The last revision that changed the verifier itself is:

~~~text
ee4b97a1f6bdde859ccac75fdbab7f8227340973
~~~

SHA-256:

~~~text
artifacts/verify_twisted_determinant_rigidity.py
1F0B198271CF33F4F67FF6D6B1140E5CC3332C93A8C65C7162E7B3476B9750F7
~~~

The local, git-addressed archive generated for this revision is:

~~~text
artifacts/twisted_determinant_rigidity_verifier_0ee48dc.zip
SHA-256 F83C70707BC78013CB035863BB619F9018CEDF7F954F1288BA936F1C58DC9631
~~~

Verify both files:

~~~powershell
Get-FileHash -Algorithm SHA256 artifacts/verify_twisted_determinant_rigidity.py, artifacts/twisted_determinant_rigidity_verifier_0ee48dc.zip
~~~

The manuscript refocus is intentionally uncommitted. The revision above
identifies the already tracked verifier, not the uncommitted referee-response
edits. A public repository URL or archive DOI must be added when the
supplement is deposited.

## Scope

artifacts/verify_twisted_determinant_rigidity.py works with fixed named edges.
Its bouquet collisions include permutations of edge names and are not claimed
to be nonconjugate after quotienting by base-shift automorphisms.
