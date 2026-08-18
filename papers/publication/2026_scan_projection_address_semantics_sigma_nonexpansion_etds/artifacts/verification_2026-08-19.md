# Independent check of the period-two example — scan_projection, 2026-08-19

Script: `verify_period_two_example.py`, in this directory.

The paper's central negative claim is that the phase qualification cannot be dropped: a
period-two survivor is exhibited whose pair-collision Poisson mean differs between the two
depth classes, so the collision count has no full-sequence weak limit under the natural
phase-free normalisation. That conclusion rests entirely on one worked example, so the
example is what was checked.

## What was computed, and independently of what

Since the Poisson mean is `(alpha^2 / 2)` times `c_{2,phase}`, the paper asserts

    lim_{m -> inf, (m-1) = phase mod 2}  S_2(m) * (3/sqrt5)^(m-1)  =  c_{2,phase}

for `S_2(m)` the Renyi pair power sum of the depth-`m` conditioned survivor law. That was
computed **directly from the chain**, not from the paper's spectral formulas:

    sum_x mu_m(x)^2 = (pi^(2))^T B_2^(m-1) 1      with (B_s)_ij = (K_ij)^s
    Z_m             = pi^T   B_1^(m-1) 1
    S_2(m)          = [sum_x mu_m(x)^2] / Z_m^2

Every quantity is an exact rational until the final irrational normalisation, which is done
in 60-digit decimal.

## Controls

- `pi K = pi` for `pi = (21,16,16,36)/89`, exactly.
- Perron values by power iteration match both the paper's numbers and the closed form
  `rho_s = sqrt(6^-s + 12^-s)`: `rho_1 = 1/2`, `rho_2 = sqrt5/12 = 0.186338998125`, and
  `s = 3` also agrees.
- Survival `Z_m` decreasing in `(0,1]` and `S_2(m)` in `(0,1]` for `m = 1..12`.

## Result: the constants are right, and they are exact

    phase 0 (m-1 even):  0.339266642933428266286934852261   c_20 = 953/2809
    phase 1 (m-1 odd) :  0.353272278102037780438609094409   c_21 = 267/(338 sqrt5)

Agreement holds to the full 60-digit precision at every depth from `m = 2` to `m = 90`. The
two Poisson means `953/5618` and `267/(676 sqrt5)` are `0.169633321467` and `0.176636139051`
— unequal, a ratio of `1.0413`, and each exactly half its `c` constant as the theorem
requires. The negative conclusion stands.

## The example is stronger than the paper states

The constants are not merely limits. They are attained **exactly at every depth**, already
at `m = 2` and `m = 3`. The reason is spectral: the killed matrix

    B_s = [[0, t, t], [r, 0, 0], [v, 0, 0]]

squares to a block form whose two-by-two block `[[tr, tr], [tv, tv]]` is singular, so `B_s`
has spectrum `{+rho_s, -rho_s, 0}` and the subdominant modulus is **exactly zero**. There is
no error term to control for this example at all.

The paper presents it as a limit statement accompanied by a total-variation error bound.
That is not wrong, but the example is bulletproof in a stronger way than claimed, and saying
so would cost one sentence and remove any question of how large `m` must be before the two
means separate. They separate at the smallest depth at which the statement makes sense.

## A note on my own first run

The first version of this script reported FAIL. The theorem was fine; the test was not. I
required the error to shrink monotonically, but the error reaches the arithmetic floor
immediately, after which the residual is rounding noise that drifts upward — `3.3e-59` to
`4.0e-59` — and monotonicity there is meaningless. The criterion now judges convergence only
above a `1e-50` floor. Reading the FAIL flag rather than the numbers next to it would have
produced a false alarm against a correct paper.
