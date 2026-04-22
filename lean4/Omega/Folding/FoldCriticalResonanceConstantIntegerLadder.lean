import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace Omega.Folding

/-- The canonical representative `k_m(u)` modulo `F_{m+2}`. -/
def foldCriticalResonanceIntegerRepresentative (u : ℤ) (m : ℕ) : ℤ :=
  Int.emod (u * Nat.fib m) (Nat.fib (m + 2))

/-- Paper label: `thm:fold-critical-resonance-constant-integer-ladder`.
This Lean theorem records the arithmetic representative used in the integer resonance ladder:
`k_m(u)` is the standard residue class of `u F_m` modulo `F_{m+2}` and lies in the canonical
half-open interval. -/
theorem paper_fold_critical_resonance_constant_integer_ladder (u : ℤ) :
    ∀ m : ℕ, 1 ≤ m →
      0 ≤ foldCriticalResonanceIntegerRepresentative u m ∧
        foldCriticalResonanceIntegerRepresentative u m < Nat.fib (m + 2) ∧
        foldCriticalResonanceIntegerRepresentative u m ≡ u * Nat.fib m [ZMOD Nat.fib (m + 2)] := by
  intro m hm
  have hFibPos : 0 < (Nat.fib (m + 2) : ℤ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  refine ⟨Int.emod_nonneg _ (by exact ne_of_gt hFibPos), Int.emod_lt_of_pos _ hFibPos, ?_⟩
  unfold foldCriticalResonanceIntegerRepresentative
  rw [Int.modEq_iff_dvd]
  refine ⟨(u * Nat.fib m) / Nat.fib (m + 2), ?_⟩
  have hdiv := Int.mul_ediv_add_emod (u * Nat.fib m) (Nat.fib (m + 2))
  exact (eq_sub_of_add_eq hdiv).symm

end Omega.Folding
