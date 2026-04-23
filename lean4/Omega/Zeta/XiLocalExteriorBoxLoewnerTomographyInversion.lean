import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The diagonal coefficient in the local exterior-box tomography matrix. -/
def xi_local_exterior_box_loewner_tomography_inversion_alpha (k t : ℕ) : ℝ :=
  Nat.choose (k - 2) (t - 1)

/-- The all-ones coefficient in the local exterior-box tomography matrix. -/
def xi_local_exterior_box_loewner_tomography_inversion_beta (k t : ℕ) : ℝ :=
  if 2 ≤ t then Nat.choose (k - 2) (t - 2) else 0

/-- The local Loewner log-volume readout after removing the universal constants. -/
def xi_local_exterior_box_loewner_tomography_inversion_readout
    (k t : ℕ) (L : Fin k → ℝ) (i : Fin k) : ℝ :=
  xi_local_exterior_box_loewner_tomography_inversion_alpha k t * Real.log (L i) +
    xi_local_exterior_box_loewner_tomography_inversion_beta k t * ∑ j : Fin k, Real.log (L j)

/-- Paper-facing inversion package for the local exterior-box Löwner tomography map. -/
def xiLocalExteriorBoxLoewnerTomographyInversion : Prop :=
  ∀ ⦃k t : ℕ⦄, 2 ≤ k → 1 ≤ t → t ≤ k - 1 →
    ∀ L : Fin k → ℝ, (∀ i, 0 < L i) →
      let α := xi_local_exterior_box_loewner_tomography_inversion_alpha k t
      let β := xi_local_exterior_box_loewner_tomography_inversion_beta k t
      let R := xi_local_exterior_box_loewner_tomography_inversion_readout k t L
      ∀ i : Fin k,
        R i = α * Real.log (L i) + β * ∑ j : Fin k, Real.log (L j) ∧
          Real.log (L i) =
            α⁻¹ * R i -
              β / (α * (α + (k : ℝ) * β)) * ∑ j : Fin k, R j

/-- Local exterior-box tomography is an explicit inversion problem for the coefficient matrix
`α I + β J`, where `α = choose (k - 2) (t - 1)` and `β = choose (k - 2) (t - 2)`.
    thm:xi-local-exterior-box-loewner-tomography-inversion -/
theorem paper_xi_local_exterior_box_loewner_tomography_inversion :
    xiLocalExteriorBoxLoewnerTomographyInversion := by
  intro k t hk ht htk L hL
  dsimp [xi_local_exterior_box_loewner_tomography_inversion_alpha,
    xi_local_exterior_box_loewner_tomography_inversion_beta,
    xi_local_exterior_box_loewner_tomography_inversion_readout]
  have htk' : t - 1 ≤ k - 2 := by omega
  have hα_pos_nat : 0 < Nat.choose (k - 2) (t - 1) := Nat.choose_pos htk'
  have hα_pos : 0 < (Nat.choose (k - 2) (t - 1) : ℝ) := by
    exact_mod_cast hα_pos_nat
  have hα_ne : (Nat.choose (k - 2) (t - 1) : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hβ_nonneg :
      0 ≤ (if 2 ≤ t then (Nat.choose (k - 2) (t - 2) : ℝ) else 0 : ℝ) := by
    by_cases h2 : 2 ≤ t
    · simp [h2]
    · simp [h2]
  have hαβ_ne :
      (Nat.choose (k - 2) (t - 1) : ℝ) +
          (k : ℝ) * (if 2 ≤ t then (Nat.choose (k - 2) (t - 2) : ℝ) else 0) ≠ 0 := by
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hsum_pos :
        0 <
          (Nat.choose (k - 2) (t - 1) : ℝ) +
            (k : ℝ) * (if 2 ≤ t then (Nat.choose (k - 2) (t - 2) : ℝ) else 0) := by
      have hmul_nonneg :
          0 ≤ (k : ℝ) * (if 2 ≤ t then (Nat.choose (k - 2) (t - 2) : ℝ) else 0) :=
        mul_nonneg (le_of_lt hk_pos) hβ_nonneg
      linarith
    exact ne_of_gt hsum_pos
  intro i
  refine ⟨rfl, ?_⟩
  let α : ℝ := Nat.choose (k - 2) (t - 1)
  let β : ℝ := if 2 ≤ t then Nat.choose (k - 2) (t - 2) else 0
  let total : ℝ := ∑ j : Fin k, Real.log (L j)
  have hsumR :
      ∑ j : Fin k, (α * Real.log (L j) + β * total) = (α + (k : ℝ) * β) * total := by
    calc
      ∑ j : Fin k, (α * Real.log (L j) + β * total)
          = ∑ j : Fin k, α * Real.log (L j) + ∑ j : Fin k, β * total := by
              rw [Finset.sum_add_distrib]
      _ = α * total + (k : ℝ) * (β * total) := by
            simp [total, Finset.mul_sum]
      _ = (α + (k : ℝ) * β) * total := by ring
  have hRi : α * Real.log (L i) + β * total =
      α * Real.log (L i) + β * total := rfl
  have hsumR' :
      ∑ j : Fin k,
          (xi_local_exterior_box_loewner_tomography_inversion_readout k t L j) =
        (α + (k : ℝ) * β) * total := by
    simpa [α, β, total,
      xi_local_exterior_box_loewner_tomography_inversion_readout,
      xi_local_exterior_box_loewner_tomography_inversion_alpha,
      xi_local_exterior_box_loewner_tomography_inversion_beta] using hsumR
  have hcancel_total :
      ((α + (k : ℝ) * β) * total) / (α * (α + (k : ℝ) * β)) = total / α := by
    apply (div_eq_div_iff (mul_ne_zero hα_ne hαβ_ne) hα_ne).2
    ring
  have hcancel_div :
      β / (α * (α + (k : ℝ) * β)) * ((α + (k : ℝ) * β) * total) = β * total / α := by
    calc
      β / (α * (α + (k : ℝ) * β)) * ((α + (k : ℝ) * β) * total) =
          β * (((α + (k : ℝ) * β) * total) / (α * (α + (k : ℝ) * β))) := by
            ring
      _ = β * (total / α) := by rw [hcancel_total]
      _ = β * total / α := by ring
  have hcancel :
      β / (α * (α + (k : ℝ) * β)) * ((α + (k : ℝ) * β) * total) = α⁻¹ * β * total := by
    rw [hcancel_div]
    ring
  calc
    Real.log (L i)
        = α⁻¹ * (α * Real.log (L i)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul]
    _ = α⁻¹ * (α * Real.log (L i) + β * total) -
          α⁻¹ * β * total := by
            ring
    _ = α⁻¹ * (α * Real.log (L i) + β * total) -
          β / (α * (α + (k : ℝ) * β)) * ((α + (k : ℝ) * β) * total) := by
            rw [← hcancel]
    _ = α⁻¹ * xi_local_exterior_box_loewner_tomography_inversion_readout k t L i -
          β / (α * (α + (k : ℝ) * β)) * ((α + (k : ℝ) * β) * total) := by
            rfl
    _ = α⁻¹ * xi_local_exterior_box_loewner_tomography_inversion_readout k t L i -
          β / (α * (α + (k : ℝ) * β)) *
            ∑ j : Fin k, xi_local_exterior_box_loewner_tomography_inversion_readout k t L j := by
            rw [← hsumR']

end

end Omega.Zeta
