import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-smith-staircase-rigidity-distinct`. -/
theorem paper_xi_smith_staircase_rigidity_distinct
    (q : ℕ) (a : Fin (q + 1) → ℕ) (hbound : ∀ i, a i ≤ q)
    (hinj : Function.Injective a) :
    Set.range a = Set.Icc 0 q := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    exact ⟨Nat.zero_le _, hbound i⟩
  · intro x hx
    let f : Fin (q + 1) → Fin (q + 1) := fun i =>
      ⟨a i, Nat.lt_succ_of_le (hbound i)⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      apply hinj
      exact congrArg Fin.val hij
    have hf_surj : Function.Surjective f := (Finite.injective_iff_surjective).1 hf_inj
    rcases hf_surj ⟨x, Nat.lt_succ_of_le hx.2⟩ with ⟨i, hi⟩
    exact ⟨i, congrArg Fin.val hi⟩

end Omega.Zeta
