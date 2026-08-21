# Reproduction

The article's claims are proved analytically in the manuscript. The numerical
calculation below is a consistency check and is not used as a premise of a
theorem. The exact symbolic calculation independently reconstructs the worked
example from its transition data; it does not replace the manuscript's general
arguments.

## Direct period-two asymptotic check

Set the working directory to
`papers/publication/2026_scan_projection_address_semantics_sigma_nonexpansion_etds/`,
then run:

    python artifacts/verify_period_two_example.py

The three preliminary controls check exactly that the displayed stationary
distribution satisfies `pi K = pi`, compare power-iteration Perron values with
`rho_1 = 1/2`, `rho_2 = sqrt(5)/12`, and
`rho_s = sqrt(6^(-s) + 12^(-s))`, and verify through `m = 12` that the survival
mass decreases in `(0,1]` while `S_2(m)` remains a valid power sum.

The decisive calculation constructs the unnormalised survivor power sums from
the rational transition matrix, conditions them to obtain `S_2(m)`, and checks
the two parity subsequences through `m = 90` against

    c_2,0 = 953/2809
    c_2,1 = 267/(338 sqrt(5)).

All quantities are rational until the final 60-digit Decimal normalization.
Expect all three controls to print `PASS`, the last phase-0 error at `m = 89`
to be `3.600e-59`, the last phase-1 error at `m = 90` to be `4.000e-59`, and

    even class  953/5618        = 0.169633321467
    odd  class  267/(676 sqrt5) = 0.176636139051
    claimed means agree with derived constants: True
      -> PASS

followed by

    SUMMARY {'controls': True, 'two constants': True, 'means differ': True}

and exit status 0. The recorded run took about 0.6 seconds and uses only the
Python standard library. A reader may conclude that the transition data
reproduce two distinct phase-resolved Poisson means and the stated constants
to the arithmetic floor in this worked example. This finite-depth calculation
does not prove the limiting theorem.

The theorem-level negative control is:

    python artifacts/verify_period_two_example.py --negative-control

It changes only the claimed even Poisson mean from `953/5618` to the incorrect
`954/5618`; it does not alter the transition matrix, safe-state indices,
recurrence, Perron calculation, or asymptotic constants. The claimed value is
then compared with the independently checked identity
`mean_even = c_2,0 / 2`. Expect the earlier controls and asymptotic check still
to pass, followed by

    NEGATIVE CONTROL  claimed even mean 953/5618 -> 954/5618
    CLAIM  the two Poisson means are different
        even class  954/5618        = 0.169811320755
        odd  class  267/(676 sqrt5) = 0.176636139051
        mean_even = c_20 / 2 ? False
        mean_odd  = c_21 / 2 ? True
        claimed means agree with derived constants: False
      -> FAIL

and

    SUMMARY {'controls': True, 'two constants': True, 'means differ': False}

with exit status 1. The recorded run took about 0.5 seconds. This shows that
the check rejects a wrong theorem constant while leaving the program's
mathematical machinery intact.

## Exact derivation of the period-two constants

From the same article directory, run:

    python artifacts/reproduce_period_two_constants.py

Using SymPy, the script takes only the transition matrix `K`, the hole/safe
split, and the two cyclic classes as mathematical inputs. It solves for `pi`,
constructs the killed entrywise powers, derives exact left and right Perron
data, evaluates the phase-resolved amplitudes and collision constants, and
computes the Renyi rate. It also applies an ordinary rank-one Perron projection
as a phase-blind control.

Expect the exact output to include

    pi = (21/89, 16/89, 16/89, 36/89)
    rho_1 = 1/2
    rho_2 = sqrt(5)/12
    c_2,0 = 953/2809
    c_2,1 = 267/(338*sqrt(5)) [simplified: 267*sqrt(5)/1690]
    h_2,H = log(3*sqrt(5)/5) = log(3/sqrt(5))
    phase-resolved constants distinct: True
    phase-blind phase 0 = phase-blind phase 1: True

and exit status 0. The recorded run took about 0.7 seconds and requires SymPy.
The result shows that the stationary, spectral, amplitude, rate, and collision
constants are derived from the example data rather than copied as unchecked
output, and that discarding the cyclic projectors erases the phase distinction.

## Automated artifact checks

From the same article directory, run:

    python -m unittest discover -s artifacts -p "test_*.py" -v

The tests execute the exact symbolic reproduction script and assert its
phase-resolved and phase-blind outputs. They also execute the direct verifier
with `--negative-control` and require the explicit failing verdict and exit
status 1. Expect

    test_period_two_negative_control_rejects_wrong_claimed_mean ... ok
    test_prints_phase_resolved_values_and_phase_blind_control ... ok

    Ran 2 tests

    OK

with exit status 0. The recorded run took about 1.1 seconds. This confirms that
both the positive symbolic derivation and the theorem-level negative control
remain executable with their expected verdicts.
