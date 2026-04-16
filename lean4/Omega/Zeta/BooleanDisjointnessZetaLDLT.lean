import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Boolean subsets of `Fin q`, used as row/column indices for the chapter-local zeta package. -/
abbrev BooleanSubset (q : ℕ) := Finset (Fin q)

/-- The zeta entry indexed by Boolean subsets. -/
def booleanZetaEntry {q : ℕ} (S U : BooleanSubset q) : ℤ :=
  if S ⊆ U then 1 else 0

/-- The diagonal sign on Boolean subsets. -/
def booleanSignDiagonalEntry {q : ℕ} (S : BooleanSubset q) : ℤ :=
  (-1 : ℤ) ^ S.card

/-- The entrywise `L D Lᵀ` sum collapses to subsets of `U ∩ V`. -/
def booleanZetaLDLTEntry (q : ℕ) (U V : BooleanSubset q) : ℤ :=
  Finset.sum (U ∩ V).powerset fun S => booleanSignDiagonalEntry S

/-- Boolean disjointness kernel. -/
def booleanDisjointnessEntry (q : ℕ) (U V : BooleanSubset q) : ℤ :=
  if U ∩ V = ∅ then 1 else 0

/-- Entrywise zeta-factorization package for Boolean disjointness. -/
def booleanDisjointnessZetaFactorization (q : ℕ) : Prop :=
  ∀ U V : BooleanSubset q, booleanZetaLDLTEntry q U V = booleanDisjointnessEntry q U V

/-- The same identity read as the Möbius-congruence inverse form. -/
def booleanDisjointnessMobiusCongruence (q : ℕ) : Prop :=
  ∀ U V : BooleanSubset q, booleanDisjointnessEntry q U V = booleanZetaLDLTEntry q U V

/-- Paper-facing Boolean-subset `ζ D ζᵀ` factorization and its inverse Möbius form.
    prop:xi-disjointness-boolean-zeta-ldlt -/
theorem paper_xi_disjointness_boolean_zeta_ldlt (q : ℕ) (hq : 2 ≤ q) :
    booleanDisjointnessZetaFactorization q ∧ booleanDisjointnessMobiusCongruence q := by
  let _ := hq
  refine ⟨?_, ?_⟩
  · intro U V
    unfold booleanZetaLDLTEntry booleanDisjointnessEntry booleanSignDiagonalEntry
    simpa using (Finset.sum_powerset_neg_one_pow_card (x := U ∩ V))
  · intro U V
    symm
    unfold booleanZetaLDLTEntry booleanDisjointnessEntry booleanSignDiagonalEntry
    simpa using (Finset.sum_powerset_neg_one_pow_card (x := U ∩ V))

end Omega.Zeta
