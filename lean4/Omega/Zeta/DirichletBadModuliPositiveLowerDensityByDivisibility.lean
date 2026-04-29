import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-dirichlet-bad-moduli-positive-lower-density-by-divisibility`.
Multiples of a fixed positive bad modulus give the finite counting lower bound, and the
reciprocal of the modulus is a positive rational density witness. -/
theorem paper_xi_dirichlet_bad_moduli_positive_lower_density_by_divisibility
    (B : ℕ → Prop) [DecidablePred B] (m0 : ℕ) (hm0_pos : 0 < m0) (hm0_mem : B m0)
    (hmul : ∀ r : ℕ, 1 ≤ r → B (r * m0)) :
    (∀ X : ℕ, X / m0 ≤ ((Finset.Icc 1 X).filter B).card) ∧
      ∃ c : ℚ, 0 < c ∧ c = (1 : ℚ) / (m0 : ℚ) := by
  have _ : B m0 := hm0_mem
  refine ⟨?_, ?_⟩
  · intro X
    let source := Finset.Icc 1 (X / m0)
    let target := (Finset.Icc 1 X).filter B
    have hsource_card : source.card = X / m0 := by
      simp [source, Nat.card_Icc]
    have hcount : source.card ≤ target.card := by
      apply Finset.card_le_card_of_injOn (fun r : ℕ => r * m0)
      · intro r hr
        have hrIcc : r ∈ Finset.Icc 1 (X / m0) := by
          simpa [source] using hr
        have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
        have hr_le : r ≤ X / m0 := (Finset.mem_Icc.mp hrIcc).2
        have h_lower : 1 ≤ r * m0 := by
          nlinarith [Nat.mul_le_mul hr_ge hm0_pos]
        have h_upper : r * m0 ≤ X := (Nat.le_div_iff_mul_le hm0_pos).mp hr_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩, hmul r hr_ge⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_right hm0_pos h
    simpa [source, target, hsource_card] using hcount
  · refine ⟨(1 : ℚ) / (m0 : ℚ), ?_, rfl⟩
    exact div_pos zero_lt_one (Nat.cast_pos.mpr hm0_pos)

end Omega.Zeta
