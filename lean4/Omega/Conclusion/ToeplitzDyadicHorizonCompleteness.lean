import Mathlib.Tactic

namespace Omega.Conclusion

/-- The top dyadic truncation already captures the full Toeplitz--PSD audit, so checking every
dyadic block up to level `K` is equivalent to checking all truncation orders. The monotonicity and
`2 ^ K = 2 * D` bookkeeping are part of the paper-facing input package. -/
theorem paper_conclusion_toeplitz_dyadic_horizon_completeness (D K : Nat) (P : Nat → Prop)
    (hK : 2 ^ K = 2 * D)
    (hMonotone : ∀ {m n : Nat}, m ≤ n → P n → P m)
    (hCollapse : P (2 ^ K) ↔ ∀ N : Nat, P N) :
    ((∀ k : Nat, k ≤ K → P (2 ^ k)) ↔ ∀ N : Nat, P N) := by
  let _ : 2 ^ K = 2 * D := hK
  constructor
  · intro hDyadic
    exact hCollapse.mp (hDyadic K le_rfl)
  · intro hAll k hk
    have hTop : P (2 ^ K) := hCollapse.mpr hAll
    exact hMonotone (Nat.pow_le_pow_right (by omega) hk) hTop

end Omega.Conclusion
