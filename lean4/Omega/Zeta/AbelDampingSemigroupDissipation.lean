import Mathlib

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Exponential damping weight for the `n`-th coefficient. -/
def abel_damping_semigroup_dissipation_weight (b δ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(δ * (n : ℝ) * Real.log b))

/-- Damping action on a finite coefficient vector. -/
def abel_damping_semigroup_dissipation_apply (b δ : ℝ) {m : ℕ} (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i => abel_damping_semigroup_dissipation_weight b δ i.1 * a i

/-- Weighted square-energy of the damped coefficients. -/
def abel_damping_semigroup_dissipation_energy (b δ : ℝ) {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ i, abel_damping_semigroup_dissipation_weight b (2 * δ) i.1 * (a i) ^ 2

/-- Coefficientwise generator of the damping flow. -/
def abel_damping_semigroup_dissipation_generator (b δ : ℝ) {m : ℕ} (a : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  (-(i : ℝ) * Real.log b) * abel_damping_semigroup_dissipation_apply b δ a i

/-- Dissipation term appearing in the energy derivative. -/
def abel_damping_semigroup_dissipation_term (b δ : ℝ) {m : ℕ} (a : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  (-(2 : ℝ) * (i : ℝ) * Real.log b) *
    abel_damping_semigroup_dissipation_weight b (2 * δ) i.1 * (a i) ^ 2

/-- Total energy dissipation. -/
def abel_damping_semigroup_dissipation_total (b δ : ℝ) {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ i, abel_damping_semigroup_dissipation_term b δ a i

theorem paper_abel_damping_semigroup_dissipation {m : ℕ} (b : ℝ) (hb : 1 ≤ b)
    (δ₁ δ₂ δ : ℝ) (hδ : 0 ≤ δ) (a : Fin m → ℝ) :
    abel_damping_semigroup_dissipation_apply b (δ₁ + δ₂) a =
      abel_damping_semigroup_dissipation_apply b δ₁
        (abel_damping_semigroup_dissipation_apply b δ₂ a) ∧
    abel_damping_semigroup_dissipation_energy b δ a ≤
      abel_damping_semigroup_dissipation_energy b 0 a ∧
    (∀ i : Fin m,
      HasDerivAt (fun ε =>
          abel_damping_semigroup_dissipation_apply b ε a i)
        (abel_damping_semigroup_dissipation_generator b δ a i) δ) ∧
    HasDerivAt (fun ε => abel_damping_semigroup_dissipation_energy b ε a)
      (abel_damping_semigroup_dissipation_total b δ a) δ := by
  constructor
  · funext i
    unfold abel_damping_semigroup_dissipation_apply
    unfold abel_damping_semigroup_dissipation_weight
    have hsplit :
        -((δ₁ + δ₂) * (i : ℝ) * Real.log b) =
          -(δ₁ * (i : ℝ) * Real.log b) + -(δ₂ * (i : ℝ) * Real.log b) := by
      ring
    rw [hsplit, Real.exp_add]
    ring
  constructor
  · have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
    have hlog_nonneg : 0 ≤ Real.log b := by
      rw [← Real.one_le_exp_iff, Real.exp_log hbpos]
      exact hb
    calc
      abel_damping_semigroup_dissipation_energy b δ a
          = ∑ i, abel_damping_semigroup_dissipation_weight b (2 * δ) i.1 * (a i) ^ 2 := rfl
      _ ≤ ∑ i, 1 * (a i) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hexp_le :
            abel_damping_semigroup_dissipation_weight b (2 * δ) i.1 ≤ 1 := by
          unfold abel_damping_semigroup_dissipation_weight
          rw [Real.exp_le_one_iff]
          have hi_nonneg : 0 ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i.1
          have hmul_nonneg : 0 ≤ 2 * δ * (i : ℝ) * Real.log b := by
            have htwo : (0 : ℝ) ≤ 2 := by norm_num
            exact mul_nonneg (mul_nonneg (mul_nonneg htwo hδ) hi_nonneg) hlog_nonneg
          linarith
        exact mul_le_mul_of_nonneg_right hexp_le (sq_nonneg (a i))
      _ = abel_damping_semigroup_dissipation_energy b 0 a := by
        simp [abel_damping_semigroup_dissipation_energy,
          abel_damping_semigroup_dissipation_weight]
  constructor
  · intro i
    have hinner :
        HasDerivAt (fun ε : ℝ => ε * (-(i : ℝ) * Real.log b))
          (-(i : ℝ) * Real.log b) δ := by
      simpa using (hasDerivAt_id δ).mul_const (-(i : ℝ) * Real.log b)
    have hweight :
        HasDerivAt
          (fun ε : ℝ => abel_damping_semigroup_dissipation_weight b ε i.1)
          (abel_damping_semigroup_dissipation_weight b δ i.1 *
            (-(i : ℝ) * Real.log b)) δ := by
      convert hinner.exp using 1
      · funext ε
        unfold abel_damping_semigroup_dissipation_weight
        congr 1
        ring
      · unfold abel_damping_semigroup_dissipation_weight
        ring
    simpa [abel_damping_semigroup_dissipation_generator,
      abel_damping_semigroup_dissipation_apply, mul_assoc, mul_left_comm, mul_comm] using
      hweight.mul_const (a i)
  · have hterm :
        ∀ i ∈ (Finset.univ : Finset (Fin m)),
          HasDerivAt (fun ε =>
              abel_damping_semigroup_dissipation_weight b (2 * ε) i.1 * (a i) ^ 2)
            (abel_damping_semigroup_dissipation_term b δ a i) δ := by
      intro i hi
      have hinner :
          HasDerivAt (fun ε : ℝ => ε * (-(2 : ℝ) * (i : ℝ) * Real.log b))
            (-(2 : ℝ) * (i : ℝ) * Real.log b) δ := by
        simpa using (hasDerivAt_id δ).mul_const (-(2 : ℝ) * (i : ℝ) * Real.log b)
      have hweight :
          HasDerivAt
            (fun ε : ℝ => abel_damping_semigroup_dissipation_weight b (2 * ε) i.1)
            (abel_damping_semigroup_dissipation_weight b (2 * δ) i.1 *
              (-(2 : ℝ) * (i : ℝ) * Real.log b)) δ := by
        convert hinner.exp using 1
        · funext ε
          unfold abel_damping_semigroup_dissipation_weight
          congr 1
          ring
        · unfold abel_damping_semigroup_dissipation_weight
          ring
      simpa [abel_damping_semigroup_dissipation_term, mul_assoc, mul_left_comm, mul_comm] using
        hweight.mul_const ((a i) ^ 2)
    convert (HasDerivAt.sum (u := Finset.univ) hterm) using 1
    · funext ε
      simp [abel_damping_semigroup_dissipation_energy]

end

end Omega.Zeta
