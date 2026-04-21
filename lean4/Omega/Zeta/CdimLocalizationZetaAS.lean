import Mathlib

namespace Omega.Zeta

noncomputable def xiLocalizedCoeff (S : Finset ℕ) (n : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if p ∈ S then 1 else p ^ k)

noncomputable def xiLocalizedEulerFactor (S P : Finset ℕ) (z : ℚ) : ℚ :=
  P.prod (fun p => if p ∈ S then (1 - z)⁻¹ else (1 - (p : ℚ) * z)⁻¹)

noncomputable def xiLocalizedCorrection (S P : Finset ℕ) (z : ℚ) : ℚ :=
  P.prod (fun p => if p ∈ S then ((1 - z)⁻¹) / ((1 - (p : ℚ) * z)⁻¹) else 1)

noncomputable def xiZetaShiftFactor (P : Finset ℕ) (z : ℚ) : ℚ :=
  P.prod (fun p => (1 - (p : ℚ) * z)⁻¹)

lemma xiLocalizedCoeff_prime_pow (S : Finset ℕ) {p k : ℕ} (hp : Nat.Prime p) :
    xiLocalizedCoeff S (p ^ k) = if p ∈ S then 1 else p ^ k := by
  unfold xiLocalizedCoeff
  rw [Nat.Prime.factorization_pow hp]
  simp

lemma xi_local_factor_eq (S : Finset ℕ) (p : ℕ) (z : ℚ)
    (_hz : 1 - z ≠ 0) (hpz : 1 - (p : ℚ) * z ≠ 0) :
    (if p ∈ S then (1 - z)⁻¹ else (1 - (p : ℚ) * z)⁻¹) =
      (1 - (p : ℚ) * z)⁻¹ *
        (if p ∈ S then ((1 - z)⁻¹) / ((1 - (p : ℚ) * z)⁻¹) else 1) := by
  by_cases hpS : p ∈ S
  · simp [hpS]
    calc
      (1 - z)⁻¹ = (1 - z)⁻¹ * (((1 - (p : ℚ) * z)⁻¹) * (1 - (p : ℚ) * z)) := by
        rw [inv_mul_cancel₀ hpz, mul_one]
      _ = (1 - (p : ℚ) * z)⁻¹ * ((1 - z)⁻¹ * (1 - (p : ℚ) * z)) := by
        ring
  · simp [hpS]

lemma xi_localized_euler_identity (S P : Finset ℕ) (z : ℚ)
    (hz : 1 - z ≠ 0) (hP : ∀ p ∈ P, 1 - (p : ℚ) * z ≠ 0) :
    xiLocalizedEulerFactor S P z = xiZetaShiftFactor P z * xiLocalizedCorrection S P z := by
  calc
    xiLocalizedEulerFactor S P z =
        P.prod (fun p => (1 - (p : ℚ) * z)⁻¹ *
          (if p ∈ S then ((1 - z)⁻¹) / ((1 - (p : ℚ) * z)⁻¹) else 1)) := by
      unfold xiLocalizedEulerFactor
      refine Finset.prod_congr rfl ?_
      intro p hp
      exact xi_local_factor_eq S p z hz (hP p hp)
    _ = P.prod (fun p => (1 - (p : ℚ) * z)⁻¹) *
          P.prod (fun p => if p ∈ S then ((1 - z)⁻¹) / ((1 - (p : ℚ) * z)⁻¹) else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = xiZetaShiftFactor P z * xiLocalizedCorrection S P z := by
      simp [xiZetaShiftFactor, xiLocalizedCorrection]

/-- Paper label: `thm:xi-cdim-localization-zeta-AS`.
The localized coefficient is the `S`-complement prime-power part of `n`; on prime powers it is
`1` inside `S` and `p^k` outside `S`; and the finite Euler product splits into the shifted zeta
factor times the localization correction built from the same local factors. -/
theorem paper_xi_cdim_localization_zeta_as (S P : Finset ℕ) (z : ℚ)
    (hz : 1 - z ≠ 0) (hP : ∀ p ∈ P, 1 - (p : ℚ) * z ≠ 0) :
    (∀ n : ℕ,
        xiLocalizedCoeff S n =
          n.factorization.prod (fun p k => if p ∈ S then 1 else p ^ k)) ∧
      (∀ {p k : ℕ}, Nat.Prime p → xiLocalizedCoeff S (p ^ k) = if p ∈ S then 1 else p ^ k) ∧
      xiLocalizedEulerFactor S P z = xiZetaShiftFactor P z * xiLocalizedCorrection S P z := by
  refine ⟨fun n => rfl, fun hp => xiLocalizedCoeff_prime_pow S hp, ?_⟩
  exact xi_localized_euler_identity S P z hz hP

end Omega.Zeta
