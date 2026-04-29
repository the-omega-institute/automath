import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-anom-unbounded-amplification`. A non-torsion anomaly has
injective natural amplification, so two amplified moments with the same anomaly have the
same amplification factor. -/
theorem paper_pom_anom_unbounded_amplification {H : Type*} [AddCommGroup H] (a : H)
    (h_non_torsion : ∀ n : ℕ, n ≠ 0 → n • a ≠ 0) :
    ∀ q₁ q₂ : ℕ, 2 ≤ q₁ → 2 ≤ q₂ → q₁ • a = q₂ • a → q₁ = q₂ := by
  intro q₁ q₂ _ _
  have pom_anom_unbounded_amplification_zero_of_lt :
      ∀ {m n : ℕ}, m < n → m • a = n • a → (n - m) • a = 0 := by
    intro m n hlt hmn
    have hsum : m • a + (n - m) • a = n • a := by
      rw [← add_nsmul, Nat.add_sub_of_le hlt.le]
    have hsum_zero : m • a + (n - m) • a = m • a + 0 := by
      rw [hsum, ← hmn]
      simp
    exact add_left_cancel hsum_zero
  intro heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hzero := pom_anom_unbounded_amplification_zero_of_lt hlt heq
    exact h_non_torsion (q₂ - q₁) (Nat.sub_ne_zero_of_lt hlt) hzero
  · have hzero := pom_anom_unbounded_amplification_zero_of_lt hgt heq.symm
    exact h_non_torsion (q₁ - q₂) (Nat.sub_ne_zero_of_lt hgt) hzero

end Omega.POM
