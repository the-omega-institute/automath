import Omega.Conclusion.ScreenAuditGapSupermodularity
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Diminishing returns for the one-step drop in the audit gap along a monotone submodular rank
function.
    cor:conclusion-screen-audit-marginal-diminishing-returns -/
theorem paper_conclusion_screen_audit_marginal_diminishing_returns {α : Type*} [DecidableEq α]
    (ρ : ℕ) (r : Finset α → ℕ) (hρ : ∀ s, r s ≤ ρ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    ∀ {A B : Finset α} {e : α}, A ⊆ B → e ∉ B →
      Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r A -
          Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r (insert e A) ≥
        Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r B -
          Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r (insert e B) := by
  intro A B e hAB heB
  have hinter : insert e A ∩ B = A := by
    ext x
    constructor
    · intro hx
      simp only [mem_inter, mem_insert] at hx
      rcases hx with ⟨hx, hxB⟩
      rcases hx with rfl | hxA
      · exact False.elim (heB hxB)
      · exact hxA
    · intro hxA
      have hxB : x ∈ B := hAB hxA
      simp [hxA, hxB]
  have hunion : insert e A ∪ B = insert e B := by
    ext x
    constructor
    · intro hx
      simp only [mem_union, mem_insert] at hx ⊢
      rcases hx with hx | hxB
      · rcases hx with rfl | hxA
        · exact Or.inl rfl
        · exact Or.inr (hAB hxA)
      · exact Or.inr hxB
    · intro hx
      simp only [mem_union, mem_insert] at hx ⊢
      rcases hx with rfl | hxB
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hxB
  have hsub' := hsub (insert e A) B
  rw [hinter, hunion] at hsub'
  have hA : r A ≤ ρ := hρ A
  have hB : r B ≤ ρ := hρ B
  have hAe : r (insert e A) ≤ ρ := hρ (insert e A)
  have hBe : r (insert e B) ≤ ρ := hρ (insert e B)
  have hAmono : r A ≤ r (insert e A) := hmono (subset_insert e A)
  have hBmono : r B ≤ r (insert e B) := hmono (subset_insert e B)
  dsimp [Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap]
  omega

end Omega.Conclusion
