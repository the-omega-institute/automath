import Omega.Conclusion.ScreenAuditGapSupermodularity
import Mathlib.Tactic

namespace Omega.Conclusion.ScreenAtomicValueAntitone

open Finset

variable {α : Type*} [DecidableEq α]

/--
Single-element marginal rank gain.
This abstracts the quantity `ν_S(e)` from
`cor:conclusion-fixedresolution-screen-atomic-value-antitone`.
-/
def MarginalValue (r : Finset α → ℕ) (s : Finset α) (e : α) : ℕ :=
  r (insert e s) - r s

/-- Abstract closure predicate encoded by zero marginal gain. -/
def InClosure (r : Finset α → ℕ) (s : Finset α) (e : α) : Prop :=
  r (insert e s) = r s

theorem marginalValue_eq_zero_iff_inClosure
    (r : Finset α → ℕ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t) :
    ∀ s e, MarginalValue r s e = 0 ↔ InClosure r s e := by
  intro s e
  dsimp [MarginalValue, InClosure]
  have hs : r s ≤ r (insert e s) := hmono (by simp)
  omega

theorem marginalValue_eq_one_iff_not_inClosure
    (r : Finset α → ℕ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hstep : ∀ s e, r (insert e s) ≤ r s + 1) :
    ∀ s e, MarginalValue r s e = 1 ↔ ¬ InClosure r s e := by
  intro s e
  dsimp [MarginalValue, InClosure]
  have hs : r s ≤ r (insert e s) := hmono (by simp)
  have hstep' := hstep s e
  omega

theorem marginalValue_antitone
    (r : Finset α → ℕ)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t)
    {s t : Finset α} {e : α}
    (hst : s ⊆ t) (he : e ∉ t) :
    MarginalValue r t e ≤ MarginalValue r s e := by
  have hinter : insert e s ∩ t = s := by
    ext x
    constructor
    · intro hx
      simp only [mem_inter, mem_insert] at hx
      rcases hx with ⟨hxs, hxt⟩
      rcases hxs with hxe | hxs
      · subst hxe
        exact False.elim (he hxt)
      · exact hxs
    · intro hxs
      have hxt : x ∈ t := hst hxs
      simp [hxs, hxt]
  have hunion : insert e s ∪ t = insert e t := by
    ext x
    constructor
    · intro hx
      simp only [mem_union, mem_insert] at hx ⊢
      rcases hx with hx | hxt
      · rcases hx with hxe | hxs
        · exact Or.inl hxe
        · exact Or.inr (hst hxs)
      · exact Or.inr hxt
    · intro hx
      simp only [mem_union, mem_insert] at hx ⊢
      rcases hx with hxe | hxt
      · exact Or.inl (Or.inl hxe)
      · exact Or.inr hxt
  have h := hsub (insert e s) t
  rw [hinter, hunion] at h
  dsimp [MarginalValue]
  omega

/--
Paper-facing seed theorem for
`cor:conclusion-fixedresolution-screen-atomic-value-antitone`.
-/
theorem paper_conclusion_fixedresolution_screen_atomic_value_antitone_seeds
    (r : Finset α → ℕ)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    ∀ {s t : Finset α} {e : α}, s ⊆ t → e ∉ t → MarginalValue r t e ≤ MarginalValue r s e := by
  intro s t e hst he
  exact marginalValue_antitone r hsub hst he

/--
Paper-facing package theorem for
`cor:conclusion-fixedresolution-screen-atomic-value-antitone`.
-/
theorem paper_conclusion_fixedresolution_screen_atomic_value_antitone_package
    (r : Finset α → ℕ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hstep : ∀ s e, r (insert e s) ≤ r s + 1)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    (∀ {s t : Finset α} {e : α}, s ⊆ t → e ∉ t → MarginalValue r t e ≤ MarginalValue r s e) ∧
      (∀ s e, MarginalValue r s e = 0 ↔ InClosure r s e) ∧
      ∀ s e, MarginalValue r s e = 1 ↔ ¬ InClosure r s e := by
  constructor
  · intro s t e hst he
    exact marginalValue_antitone r hsub hst he
  constructor
  · intro s e
    exact marginalValue_eq_zero_iff_inClosure r hmono s e
  · intro s e
    exact marginalValue_eq_one_iff_not_inClosure r hmono hstep s e

end Omega.Conclusion.ScreenAtomicValueAntitone
