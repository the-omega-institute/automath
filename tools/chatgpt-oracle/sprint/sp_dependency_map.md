# Dependency map for the rebuilt Zeckendorf carry paper

This map was written before editing the publication directory.  It records the
results retained in the rebuilt manuscript and follows each proof dependency
transitively.  The EML/Richardson sections, the L0/L1/L2 presentation, and the
arbitrary-cover construction are deliberately absent from every dependency
chain below.

## Foundational definitions and interfaces

* `def:fold` (finite fold, `Omega_m`, `X_m`, `Val_m`, `Fold_m`, stable
  Zeckendorf words) is definitional.  It uses only the Fibonacci convention
  `F_1=1,F_2=2,F_{k+2}=F_{k+1}+F_k`.
* `lem:greedy-zeckendorf-normalizer` is the classical Zeckendorf uniqueness
  and computability input (`Zeckendorf1972`).
* `prop:finite-zeckendorf-residue-interface` depends on
  `def:fold` and `lem:greedy-zeckendorf-normalizer`; it proves that `Val_m` is
  a bijection onto the residue representatives and that `Fold_m` is onto.
* `prop:fold-confluence` depends on
  `lem:greedy-zeckendorf-normalizer` and
  `prop:finite-zeckendorf-residue-interface`; it identifies stable equality
  with equality of ordinary valuations and finite equality with congruence
  modulo `F_{m+2}`.
* `def:collision-moment` is definitional.  Its intrinsic specialization is
  `S_q^int(m)=sum_x |Fold_m^{-1}(x)|^q`.

## Fixed-degree carry and transfer chain

* `lem:scalar-signed-fibonacci-exit-classification` is elementary.  It uses
  only the scalar carry update `tau_a(p,r)=(r,p+a-r)` and the alphabet
  `a in {-1,0,1}`.  It proves the two forward-invariant exit classes.
* `lem:coordinatewise-signed-fibonacci-exit-deletion` depends on the scalar
  exit lemma.  Its carry identity and the implication
  `target congruence => final state (sigma,0)` use only the Fibonacci
  recurrence, the elementary carry bounds, and `gcd(F_n,F_{n+1})=1`.
* `lem:bounded-signed-fibonacci-carry` depends on
  `def:fold`, `prop:finite-zeckendorf-residue-interface`,
  `lem:scalar-signed-fibonacci-exit-classification`, and
  `lem:coordinatewise-signed-fibonacci-exit-deletion`.  It additionally uses
  the bound `|sum a_k F_k|<2F_{m+2}` to choose the unique target marker
  `sigma`.  It is the losslessness theorem: deleting exits discards no
  accepting path.
* `thm:audited-fixed-degree-transfer-interface` depends on
  `lem:bounded-signed-fibonacci-carry` and its two exit sublemmas.  It identifies
  the exact weighted adjacency entry of `T_q` and the initial/accepting
  vectors; no cover multiplicity or resolution-dependent state appears.
* `thm:intrinsic-fold-moment-transfer` depends on
  `thm:audited-fixed-degree-transfer-interface` (equivalently the bounded carry
  lemma) and the elementary Fibonacci transfer for `q=0`.  It concludes the
  fixed matrix formula, rational ordinary generating function, and
  constant-coefficient recurrence for every fixed `q`.
* `prop:fixed-transfer-interface-budget` depends only on the matrix formula:
  every fixed finite-state transfer sequence is exponentially bounded and
  therefore C-finite with rational ordinary generating function.
* `thm:primitive-intrinsic-moment-transfer` depends on
  `thm:intrinsic-fold-moment-transfer`, the trim of the positive-weight carry
  graph, the reachable-marker sign observation, and the zero-column loop.  The
  sign observation uses only the fold collision interpretation already proved
  in `lem:bounded-signed-fibonacci-carry`.  Strong connectivity plus the loop
  gives primitivity, and Perron--Frobenius gives the positive asymptotic and
  pressure for each fixed `q`.

## Exact second moment

* `lem:initial-second-moment-enumeration` is a direct enumeration of lengths
  `1,2,3` and uses only `F_1=1,F_2=2,F_3=3` and residues modulo `F_{n+1}`.
* `thm:intrinsic-second-moment-recurrence` depends on
  `lem:initial-second-moment-enumeration` and the `q=2` specialization of
  `thm:audited-fixed-degree-transfer-interface`: the three scalar path totals
  `A_n,B_n,D_n` and their transition equations.  It does not use primitivity,
  height estimates, covers, or any deleted section.
* `cor:polynomial-intrinsic-fibre-statistics` depends on
  `thm:intrinsic-fold-moment-transfer` only, by finite linear combination of
  fixed moment slices.

## Height chain

* `def:representation-count`/`R_n` is definitional for unrestricted Fibonacci
  subset representations using parts `F_1,...,F_n`.
* `lem:fold-fibre-representation-pairing` depends on
  `def:fold`, `prop:finite-zeckendorf-residue-interface`, and the elementary
  bijection between a fold fibre and representations of
  `F_{m+2}+r` with parts at most `F_{m+1}`.
* `lem:fibonacci-maximum-normalization-conversion` is a citation boundary
  only: it translates the convention in Kocábová--Masáková--Pelantová
  (`KMP2015`, Theorem 4.7) to `F_1=1,F_2=2`; no proof from deleted material is
  used.
* `thm:half-interval-fibonacci-representation-max` depends on the normalized
  ordinary interval maxima, the elementary recurrence for `R_n`, and interval
  containment.  It proves the shifted half-interval maximum internally.
* `thm:intrinsic-fold-fibre-height` depends on
  `lem:fold-fibre-representation-pairing` and
  `thm:half-interval-fibonacci-representation-max`; it gives
  `M_{2s-1}=F_{s+1}`, `M_{2s}=2F_s`.
* `cor:linfty-fold-entropy` depends only on
  `thm:intrinsic-fold-fibre-height` and Binet's formula.

## Nonuniformity in the moment degree

* `cor:intrinsic-all-degree-transfer-obstruction` (the concise replacement
  for the old major obstruction theorem) depends on
  `thm:intrinsic-fold-fibre-height`/`cor:linfty-fold-entropy` for
  `log M_m=(m/2)log(phi)+O(1)` and on
  `prop:fixed-transfer-interface-budget` for the fixed-transfer exponential
  bound.  The bivariate nonrationality part uses only the elementary Cauchy
  coefficient estimate for a rational formal power series and the diagonal
  lower bound `S_m^int(m)>=M_m^m`.  It does not depend on primitivity, covers,
  EML/Richardson, or hierarchy terminology.

## Explicitly cut and therefore not dependencies

The following are archived verbatim and are not input by `main.tex`:

* all EML/Odrzywolek/Richardson definitions, witness libraries, translations,
  and separation statements;
* every L0/L1/L2 hierarchy definition, theorem, and strictness presentation;
* the arbitrary computable finite-fibre cover and one-spike/factorial
  obstruction;
* protocol readout and monogenic-orbit material that served only the rejected
  hierarchy framing.

No retained result invokes any of these archived statements.
