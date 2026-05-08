# Main Theorem Package

The main paper should be organized around six theorem packages.

## Theorem 1: Scan--Projection Interface

Finite binary scans factor depth-m visible events through the finite word space `Omega_m = {0,1}^m`.

## Lemma 2: Finite Zeckendorf Section

Legal words in `X_m` represent exactly the residues `0, ..., F_{m+2}-1` under the shifted Fibonacci value map.

## Theorem 3: Golden Folding Normal Form

`Fold_m = s_m(N_m(.) mod F_{m+2})` is well-defined, computable, idempotent, surjective, and fixes `X_m`.

## Theorem 4: Cross-Resolution Compatibility

Stable prefix restrictions `pi_{m+1 -> m}: X_{m+1} -> X_m` form an inverse system. Fold-aware raw restriction is `rho_tilde_{m+1,m} = pi_{m+1 -> m} Fold_{m+1}`. Naive truncation is not assumed to commute.

## Theorem 5: Recursive Address Non-Expansion

New address-layer events satisfy `H_{L+1} subseteq G_{<=L}`, hence the cumulative algebra satisfies `G_{<=L+1} = G_{<=L}`.

## Theorem 6: Scan Clarity Boundary Estimate

The optimal prefix classification error has an exact cylinder decomposition and is bounded by boundary cylinder growth.

## Corollary 7: Auditable Stable-Type Generator

The preceding theorem packages produce the object

`(Omega_m, X_m, Fold_m, pi_{m+1->m}, rho_tilde_{m+1,m}, F_m, G_{<=L}, epsilon_m, Cert_m)`.

This is the main output of Paper I.

## Appendix B: Finite-State Audit of the Folded Sofic Factor

For each fixed depth `m`, the block factor

`Phi_m:{0,1}^Z -> X_m^Z`

has sofic image `Y_m`.  Appendix B builds a labeled de Bruijn presentation, determinizes it to a right-resolving Markov cover `K_m`, computes the cover adjacency matrix `A_m`, and records entropy, Parry data, cover zeta, and the golden-mean Parry baseline.

The key theorem is:

`h_top(Y_m) = log rho(A_m)`.

Cover-level zeta and periodic orbit counts are kept separate from intrinsic labeled-system invariants.

## Appendix C: Statistical Audit of Fold Histograms

For an empirical folded histogram `pi_hat_{m,N}`, Appendix C separates:

- exact deterministic tables: `Fold_m`, fiber multiplicities `d_m`, IID-uniform fiber law `p_m^fib`, and Parry baseline `q_m`;
- random empirical histograms;
- finite-sample TV/KL envelopes;
- cross-resolution residuals.

The key theorem is the decomposition:

`TV(pi^P_m, q_m)` is bracketed by `TV(pi_hat_{m,N}, q_m) +/- tau`,

with analogous hidden-volume and cross-resolution lower bounds.  Parry agreement is treated as a baseline comparison, not as mechanism identification.

## Appendix D: Fold Multiplicity, Fiber Law, and Information Ledger

For each fixed depth `m`, Appendix D records the deterministic fold fibers

`F_m(z) = Fold_m^{-1}(z)`

and multiplicities `d_m(z)`.  It defines the exact IID-uniform fiber law

`p_m^fib(z) = d_m(z) / 2^m`,

the hidden-volume statistic `kappa_m(p)`, fiber moments `M_{m,q}`, collision probabilities, and the deterministic cross-resolution fiber residual `G_m^fib`.

The key ledger theorem is:

`H(mu) = H(pi) + kappa_m(pi) - R_m(mu)`,

where `pi = (Fold_m)_# mu` and `R_m(mu)` is the within-fiber KL residual.  The KL decomposition is:

`KL(mu | U_m) = KL(pi | p_m^fib) + R_m(mu)`.

These identities separate visible entropy, hidden fiber volume, and within-fiber nonuniformity.

## Appendix E: Exact Reproducibility Package

Appendix E specifies the executable audit package around Appendices C--D.  The deterministic core includes:

- `fold_table.json`;
- `restriction_table.json`;
- `fiber_ledger.csv`;
- `fiber_ledger_summary.csv`;
- `parry_baseline.csv`;
- `moment_spectrum.csv`;
- `cross_resolution_fib.csv`;
- canonical SHA256 hashes.

The empirical layer includes sampled windows, folded histograms, TV/KL audit tables, audit summaries, and empirical cross-resolution residuals.

The key reproducibility theorems are:

- deterministic outputs are reproducible up to canonical hashes;
- deterministic identity failures cannot be explained by sampling variability;
- reported empirical audit values are deterministic functions of saved tables once count checks and joins pass.

## Stage 46 audit target

The next audit should classify each theorem as one of:

- fully proved in the main text;
- proved modulo appendix obligations;
- definition/proposition rather than theorem;
- requires additional assumptions;
- should be downgraded before submission.
