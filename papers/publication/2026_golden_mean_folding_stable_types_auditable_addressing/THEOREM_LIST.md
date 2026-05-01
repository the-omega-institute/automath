# Main Theorem Package

The main paper should be organized around six theorem packages.

## Theorem 1: Scan--Projection Interface

Finite binary scans factor depth-m visible events through the finite word space `Omega_m = {0,1}^m`.

## Theorem 2: Golden Folding Normal Form

The local carry-elimination system defining `Fold_m` is terminating, confluent, order-independent, and idempotent, with image `X_m`.

## Theorem 3: Cross-Resolution Compatibility

Fold-aware restrictions `r_{m+1,m}: X_{m+1} -> X_m` form an inverse system and commute with folding in the typed diagram. Naive truncation is not assumed to commute.

## Theorem 4: Recursive Address Non-Expansion

Addresses constructed from prior readouts and deterministic certificate bookkeeping satisfy `G_{L+1} subseteq G_L`.

## Theorem 5: Scan Clarity Boundary Estimate

The optimal prefix classification error has an exact cylinder decomposition and is bounded by boundary cylinder growth.

## Theorem 6: Auditable Stable-Type Generator

The preceding theorem packages produce the object

`(Omega_m, X_m, Fold_m, r_{m+1,m}, F_m, G_L, epsilon_m, Cert_m)`.

This is the main output of Paper I.

## Stage 39 audit target

The next audit should classify each theorem as one of:

- fully proved in the main text;
- proved modulo appendix obligations;
- definition/proposition rather than theorem;
- requires additional assumptions;
- should be downgraded before submission.
