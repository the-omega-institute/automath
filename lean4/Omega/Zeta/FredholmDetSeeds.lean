import Mathlib.Tactic

/-!
# Fredholm Determinant Seed Values

Golden-mean SFT Fredholm determinant polynomial p(z) = 1 - z - z²
evaluated at key points: p(1) = -1, discriminant = 5, p(1/2) = 1/4.
-/

namespace Omega.Zeta

/-- The Fredholm determinant polynomial p(z) = 1 - z - z² for the golden-mean SFT.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
def fredholmPoly (z : ℚ) : ℚ := 1 - z - z ^ 2

/-- p(1) = -1.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_at_one : fredholmPoly 1 = -1 := by
  unfold fredholmPoly; ring

/-- Discriminant of z² + z - 1 (i.e., -p(z)) equals 5.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_discriminant : (1 : ℚ) ^ 2 + 4 * 1 = 5 := by ring

/-- p(1/2) = 1/4.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_at_half : fredholmPoly (1 / 2) = 1 / 4 := by
  unfold fredholmPoly; ring

/-- Seed value package for the golden-mean Fredholm determinant.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem paper_fredholm_golden_mean_seeds :
    fredholmPoly 1 = -1 ∧
    (1 : ℚ) ^ 2 + 4 * 1 = 5 ∧
    fredholmPoly (1 / 2) = 1 / 4 :=
  ⟨fredholmPoly_at_one, fredholmPoly_discriminant, fredholmPoly_at_half⟩

-- Phase R608: Fredholm polynomial Vieta relations and irrationality
-- ══════════════════════════════════════════════════════════════

/-- p(0) = 1.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_at_zero : fredholmPoly 0 = 1 := by
  unfold fredholmPoly; ring

/-- Vieta sum: if z₁, z₂ are the two roots of z² + z - 1 = 0, then z₁ + z₂ = -1.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_vieta_sum :
    ∀ z₁ z₂ : ℚ, fredholmPoly z₁ = 0 → fredholmPoly z₂ = 0 → z₁ ≠ z₂ →
      z₁ + z₂ = -1 := by
  intro z₁ z₂ h1 h2 hne
  unfold fredholmPoly at h1 h2
  have hsub : z₁ ^ 2 - z₂ ^ 2 = z₂ - z₁ := by linarith
  have hdiff : (z₁ - z₂) * (z₁ + z₂) = -(z₁ - z₂) := by nlinarith [hsub]
  have hne' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
  have := mul_left_cancel₀ hne' (show (z₁ - z₂) * (z₁ + z₂) = (z₁ - z₂) * (-1) by linarith [hdiff])
  linarith

/-- Vieta product: z₁ · z₂ = -1.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_vieta_product :
    ∀ z₁ z₂ : ℚ, fredholmPoly z₁ = 0 → fredholmPoly z₂ = 0 → z₁ ≠ z₂ →
      z₁ * z₂ = -1 := by
  intro z₁ z₂ h1 h2 hne
  unfold fredholmPoly at h1 h2
  have hsum := fredholmPoly_vieta_sum z₁ z₂ (by unfold fredholmPoly; linarith)
    (by unfold fredholmPoly; linarith) hne
  nlinarith [h1, hsum]

/-- No rational root: fredholmPoly z ≠ 0 for all z : ℚ.
    Proof: z² + z - 1 = 0 → (2z+1)² = 5, but 5 is not a square in ℚ.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_no_rational_root :
    ∀ z : ℚ, fredholmPoly z ≠ 0 := by
  intro z hz
  unfold fredholmPoly at hz
  have h5 : (2 * z + 1) ^ 2 = 5 := by nlinarith
  -- Lift to ℤ: (2·num + den)² = 5·den²
  have hzq := z.num_div_den
  have hd_ne : (z.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z.den_ne_zero
  rw [← hzq] at h5
  have h5z : (2 * z.num + z.den) ^ 2 = 5 * (z.den : ℤ) ^ 2 := by
    have := h5; field_simp at this
    -- this : (2 * ↑z.num + ↑z.den) ^ 2 = ↑z.den ^ 2 * 5  (in ℚ)
    have h_int : (((2 * z.num + z.den) ^ 2 : ℤ) : ℚ) = ((5 * (z.den : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h_int
  set a := 2 * z.num + (z.den : ℤ) with ha_def
  have h5a2 : (5 : ℤ) ∣ a ^ 2 := ⟨(z.den : ℤ) ^ 2, h5z⟩
  have h5a : (5 : ℤ) ∣ a := Prime.dvd_of_dvd_pow (by decide) h5a2
  obtain ⟨k, hk⟩ := h5a
  have h5d2 : (5 : ℤ) ∣ (z.den : ℤ) ^ 2 := by
    have ha_eq : a ^ 2 = (5 * k) ^ 2 := by rw [hk]
    have : (5 * k) ^ 2 = 5 * (z.den : ℤ) ^ 2 := ha_eq ▸ h5z
    have : (z.den : ℤ) ^ 2 = 5 * k ^ 2 := by nlinarith
    exact ⟨k ^ 2, this⟩
  have h5d : (5 : ℤ) ∣ (z.den : ℤ) := Prime.dvd_of_dvd_pow (by decide) h5d2
  have h5_2num : (5 : ℤ) ∣ 2 * z.num := by omega
  have h5n : (5 : ℤ) ∣ z.num :=
    (Prime.dvd_or_dvd (by decide : Prime (5 : ℤ)) h5_2num).resolve_left (by decide)
  -- 5 divides both num.natAbs and den, contradicting coprimality
  have hcop := z.reduced
  have h5_natabs : 5 ∣ z.num.natAbs :=
    Int.natAbs_dvd_natAbs.mpr h5n
  have h5_den : 5 ∣ z.den := by exact_mod_cast h5d
  have hgcd : ¬ (z.num.natAbs.Coprime z.den) := by
    intro hc
    exact absurd (show (5 : ℕ) ∣ 1 from hc.coprime_dvd_left h5_natabs |>.coprime_dvd_right
      h5_den |>.symm ▸ dvd_refl 5) (by omega)
  exact hgcd hcop

/-- Decreasing seeds: p(0) > 0 and p(1) < 0.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_decreasing_seeds :
    fredholmPoly 0 = 1 ∧
    fredholmPoly (1/2) = 1/4 ∧
    fredholmPoly 1 = -1 ∧
    fredholmPoly (1/2) > 0 ∧
    fredholmPoly 1 < 0 := by
  refine ⟨fredholmPoly_at_zero, fredholmPoly_at_half, fredholmPoly_at_one, ?_, ?_⟩
  · rw [fredholmPoly_at_half]; norm_num
  · rw [fredholmPoly_at_one]; norm_num

/-- Paper package.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem paper_fredholm_vieta_package :
    ((1 : ℚ) ^ 2 + 4 * 1 = 5) ∧
    (fredholmPoly 0 = 1) ∧
    (fredholmPoly 1 = -1) ∧
    (fredholmPoly 0 > 0 ∧ fredholmPoly 1 < 0) ∧
    (∀ z : ℚ, fredholmPoly z ≠ 0) :=
  ⟨fredholmPoly_discriminant, fredholmPoly_at_zero, fredholmPoly_at_one,
   ⟨by rw [fredholmPoly_at_zero]; norm_num, by rw [fredholmPoly_at_one]; norm_num⟩,
   fredholmPoly_no_rational_root⟩

end Omega.Zeta
