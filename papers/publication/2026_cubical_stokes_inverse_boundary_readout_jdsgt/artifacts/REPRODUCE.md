# Reproduction

The article's claims are proved analytically in the manuscript. The numerical
calculations below are consistency checks and are not used as premises of any
theorem. The exact-arithmetic checks provide auditable instances of the
combinatorial statements; they do not replace the general proofs.

## Box extremal-value check

Set the working directory to
`papers/publication/2026_cubical_stokes_inverse_boundary_readout_jdsgt/`, then
run:

    python artifacts/verify_box_extremal_value.py

The first control evaluates the explicit affine primitive independently of the
closed form

    m(R) = (2 sum_j 1/L_j)^(-1)

on six boxes in dimensions two through four. It checks that the affine weights
sum to one, that their coefficient sup norms are equal, and that the resulting
value agrees with the formula to tolerance `1e-12`.

The numerical part formulates the two-dimensional discrete primitive problem
as a linear program with edge variables and cellwise finite-difference
constraints. It solves the problem with SciPy's `linprog` on the three boxes
`1 x 1`, `1 x 2`, and `0.5 x 3`, at each of the four meshes
`n = 6, 10, 16, 24`. Expect all affine comparisons to end in `ok`, all twelve
LP ratios to print as `1.000000`, and the final lines

    -> consistent

    SUMMARY {'affine construction': True, 'discrete LP': True}

with exit status 0. On the recorded run this took about 1.1 seconds. The check
requires NumPy and SciPy. The result confirms that the explicit construction
and an independently posed discrete optimization problem agree with the
claimed constant in these cases; the continuous equality itself is supplied
by the manuscript's upper- and lower-bound arguments.

## Anisotropic cubical-patching obstruction

From the same article directory, run:

    python artifacts/verify_cubical_patching.py

This standard-library exact-arithmetic check enumerates every nonempty subset
of a `2 x 2` anisotropic complex. It computes the cut ratio `h = 9/8`, sets
`delta = 9/4`, evaluates the atomic boundary profile, identifies all nine
atomic maximizers, and checks that every maximizer violates at least one
internal-cut capacity constraint. Expect

    h=9/8, delta=9/4, atomic profile=72
    all 9 atomic maximizers violate an internal cut

followed by nine exact rational inequalities and exit status 0. A reader may
conclude that the paper's four-cell obstruction is reproduced without
floating-point tolerances.

The script has a built-in negative control. Run:

    python artifacts/verify_cubical_patching.py --negative-control

This leaves the computed atomic profile unchanged but replaces the claimed
value `72` by the incorrect value `73`. Expect an `AssertionError` at

    assert profile == expected

and exit status 1. The default and mutated runs each took about 0.2 seconds.
Together they show that this check is sensitive to the asserted atomic value,
not merely to the executable integrity of the enumeration.

## Patching-theorem hypotheses

From the same article directory, run:

    python artifacts/verify_patching_hypotheses.py

The script uses the fixed random seed `7` to generate 60 small
sink-connected augmented dual networks satisfying the theorem's hypotheses.
For each network it enumerates the cut formula `h_K` exactly and compares it
with the minimum weighted flux norm obtained by `scipy.optimize.linprog`.
It then checks two excluded cases: a shared face with an invalid `(+1,+1)`
incidence column, and a closed component with positive total source and no
boundary face.

Expect the principal output

    tested 60, mismatches 0
    with the face repaired as a proper internal edge: h_K=1.0000 min=1.0000 equal=True
    with the (+1,+1) column present: LP min = 0.5000
    h_K=1.0   LP min=None   (LP infeasible => None, since sum v over the closed component is 2 != 0)

and exit status 0. The recorded run took about 0.7 seconds and requires SciPy
and NumPy. The first line is a finite consistency check for the stated
min-cut/max-flow identity. The two explicit failures show why reduced
incidence and sink connectivity are substantive hypotheses.
