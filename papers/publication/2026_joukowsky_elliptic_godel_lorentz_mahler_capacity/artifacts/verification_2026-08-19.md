# Independent check of the opening-deficit limit — joukowsky, 2026-08-19

Script: `verify_opening_deficit.py`, in this directory.

The abstract's headline is that for every member of the collapsed equality class,
written `d eta = (1+h) dm` with `h(conj z) = -h(z)` and `|h| <= 1`,

    lim_{s -> 0+} ( s - I(J_{e^s *} eta) ) / (2s) = (1/2) ||h||^2_{L^2(m)}

with sharp range `[0, 1/2]`. That was checked analytically and then numerically.

## The analytic route

On `|z| = |w| = 1` the Joukowsky difference factors:

    J_r(z) - J_r(w) = (z - w) ( r - r^{-1} conj(z w) ),

so `log|J_r(z)-J_r(w)|` splits into `log|z-w|` plus a term in `theta + phi` alone. With
`r = e^s`, `log|e^s - e^{-s} e^{-i psi}| = s - sum_{n>=1} e^{-2ns} cos(n psi)/n`. Writing
`hat h_n` for the Fourier coefficients of `h`:

    I_T(eta)                = - sum_{n>=1} |hat h_n|^2 / n
    iint (second factor)    = s - sum_{n>=1} (e^{-2ns}/n) Re[ hat h_n^2 ]

**The mechanism is the conjugation-oddness.** `h(-theta) = -h(theta)` forces
`conj(hat h_n) = - hat h_n`, so every coefficient is purely imaginary, `hat h_n = i b_n`.
Then `|hat h_n|^2 = b_n^2` while `Re[hat h_n^2] = -b_n^2`, so the two contributions **add**
instead of cancelling:

    s - I(J_{e^s *} eta) = sum_{n>=1} (b_n^2 / n) ( 1 - e^{-2 n s} ).

Dividing by `2s` and letting `s -> 0` sends each term to `b_n^2`, and
`sum_{n>=1} b_n^2 = (1/2) ||h||^2` because `hat h_0 = 0` and the negative modes duplicate
the positive ones. That is the theorem.

## Controls, run before anything was concluded

- **Factorisation**, checked pointwise at 20,000 random `(theta, phi, r)`: worst
  discrepancy `3.6e-15`.
- **Haar**: for `h = 0` the quadrature returns `I = s` to `3e-15` at `s = 0.05` and
  `s = 0.02`. This is an independent classical value — the ellipse with semiaxes
  `r + 1/r` and `r - 1/r` has capacity `r`, hence energy `log r = s` — so it validates the
  quadrature against something the script does not compute.
- **Closed form against direct quadrature**, so the series above is verified rather than
  assumed: at `s = 0.05` the two agree to `7e-5` for `h = sin` and `2e-5` for `h = mixed`.

## Result

Five members, each with zero conjugation-oddness defect:

| member | `(1/2)\|\|h\|\|^2` | quotient at `s = 10^-3` |
|---|---|---|
| `h = 0` | 0 | 0 exactly |
| `h = sin` | 0.25 | 0.249251 |
| `h = sin 3t` | 0.25 | 0.249251 |
| `h = mixed` | 0.08203125 | 0.081918 |
| `h = sign(sin)` | 0.4999975 | 0.498268 |

Every one approaches its target monotonically from below. The range endpoints are attained
where the paper says: `0` at `h = 0`, and `1/2` at the extreme member with `|h| = 1` a.e.

## On the residual at the extreme member

At `s = 10^-3` the extreme member is still `1.7e-3` short. **That is the predicted rate, not
a discrepancy.** For `h = sign(sin)` the coefficients decay like `b_n ~ 1/n`, so
`sum_n n b_n^2` diverges logarithmically and the deviation behaves like `s log(1/s)` rather
than `s`. At `s = 10^-3` that is of order `10^-3 * log 10^3 ~ 7e-3` times a constant, which
is what the table shows. The smooth members, whose coefficients terminate, converge linearly
and sit three orders closer. Comparing a residual against the rate the structure predicts is
the point; a bare gap would say nothing either way.
