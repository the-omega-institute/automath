import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Omega.Conclusion.S4UniversalBoundaryCarrierNonprincipalPolarization

namespace Omega.DerivedConsequences

open Omega.Conclusion

/-- The recorded polarization type of the `V₂` block `A₂`. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_v2_type : List ℕ :=
  [1, 1, 1, 1, 3, 3, 3, 3]

/-- The mixed polarization type on `M = A₂ × P`, written in nondecreasing order. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_mixed_type : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3]

/-- The degree of the mixed polarization `λ_M`. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree : ℕ :=
  (2 ^ 5 * 3 ^ 4) ^ 2

/-- Reparameterize the admissible scaling factor by `n = 6 m`, so the minimal admissible value is
`n = 6`. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_scale (m : ℕ) : ℕ :=
  6 * m

/-- The corresponding isogeny degree `deg f = n^17 / (2^5 3^4)` after writing `n = 6 m`. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree (m : ℕ) : ℕ :=
  2 ^ 12 * 3 ^ 13 * m ^ 17

/-- Concrete package for
`thm:derived-hurwitz-prym-mixed-principal-polarization-degree`. It records the `V₂` and Prym
polarization types, their mixed type, the mixed polarization degree, the factorized pullback
formula with `n = 6 m`, and the resulting minimal degree at `m = 1`, i.e. `n = 6`. -/
def derived_hurwitz_prym_mixed_principal_polarization_degree_statement : Prop :=
  derived_hurwitz_prym_mixed_principal_polarization_degree_v2_type =
      [1, 1, 1, 1, 3, 3, 3, 3] ∧
    conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type =
      [1, 1, 1, 1, 2, 2, 2, 2, 2] ∧
    derived_hurwitz_prym_mixed_principal_polarization_degree_mixed_type =
      [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3] ∧
    derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree =
      (2 ^ 5 * 3 ^ 4) ^ 2 ∧
    derived_hurwitz_prym_mixed_principal_polarization_degree_scale 1 = 6 ∧
    ∀ m : ℕ, 0 < m →
      derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m *
          (2 ^ 5 * 3 ^ 4) =
        derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 17 ∧
      derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 34 =
        derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m ^ 2 *
          derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree ∧
      2 ^ 12 * 3 ^ 13 ≤
        derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m ∧
      (derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m =
          2 ^ 12 * 3 ^ 13 ↔
        m = 1)

/-- Paper label: `thm:derived-hurwitz-prym-mixed-principal-polarization-degree`. The mixed Prym
block has polarization type `(1^8, 2^5, 3^4)`, hence degree `(2^5 * 3^4)^2`; after writing the
pullback scale as `n = 6 m`, the isogeny degree is `2^12 * 3^13 * m^17`, so the minimum
`2^12 * 3^13` occurs exactly at `m = 1`, i.e. `n = 6`. -/
theorem paper_derived_hurwitz_prym_mixed_principal_polarization_degree :
    derived_hurwitz_prym_mixed_principal_polarization_degree_statement := by
  have hPrymType :
      conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type =
        [1, 1, 1, 1, 2, 2, 2, 2, 2] := by
    exact paper_conclusion_s4_universal_boundary_carrier_nonprincipal_polarization.2.1
  refine ⟨rfl, hPrymType, rfl, rfl, rfl, ?_⟩
  intro m hm
  have hformula :
      derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m *
          (2 ^ 5 * 3 ^ 4) =
        derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 17 := by
    unfold derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree
      derived_hurwitz_prym_mixed_principal_polarization_degree_scale
    calc
      (2 ^ 12 * 3 ^ 13 * m ^ 17) * (2 ^ 5 * 3 ^ 4) = 2 ^ 17 * 3 ^ 17 * m ^ 17 := by
        ring_nf
      _ = (6 : ℕ) ^ 17 * m ^ 17 := by norm_num
      _ = (6 * m) ^ 17 := by rw [mul_pow]
  have hpullback :
      derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 34 =
        derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m ^ 2 *
          derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree := by
    calc
      derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 34 =
          derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 17 *
            derived_hurwitz_prym_mixed_principal_polarization_degree_scale m ^ 17 := by
            rw [show 34 = 17 + 17 by norm_num, pow_add]
      _ =
          (derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m *
              (2 ^ 5 * 3 ^ 4)) *
            (derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m *
              (2 ^ 5 * 3 ^ 4)) := by
            rw [hformula.symm]
      _ =
          derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m ^ 2 *
            derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree := by
            unfold derived_hurwitz_prym_mixed_principal_polarization_degree_lambda_degree
            ring_nf
  have hbound :
      2 ^ 12 * 3 ^ 13 ≤
        derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m := by
    unfold derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree
    have hm17 : 1 ≤ m ^ 17 := Nat.succ_le_of_lt (pow_pos hm 17)
    calc
      2 ^ 12 * 3 ^ 13 = (2 ^ 12 * 3 ^ 13) * 1 := by simp
      _ ≤ (2 ^ 12 * 3 ^ 13) * m ^ 17 := by
        exact Nat.mul_le_mul_left _ hm17
  have heq :
      (derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m =
          2 ^ 12 * 3 ^ 13 ↔
        m = 1) := by
    constructor
    · intro hdeg
      by_cases h1 : m = 1
      · exact h1
      · have hm_gt : 1 < m := by omega
        have hpow_gt : 1 < m ^ 17 := by
          exact Nat.one_lt_pow (by norm_num : 17 ≠ 0) hm_gt
        have hstrict :
            2 ^ 12 * 3 ^ 13 <
              derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree m := by
          unfold derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree
          calc
            2 ^ 12 * 3 ^ 13 = (2 ^ 12 * 3 ^ 13) * 1 := by simp
            _ < (2 ^ 12 * 3 ^ 13) * m ^ 17 := by
              exact Nat.mul_lt_mul_of_pos_left hpow_gt (by norm_num)
        rw [hdeg] at hstrict
        exact (lt_irrefl _ hstrict).elim
    · intro hm1
      simp [derived_hurwitz_prym_mixed_principal_polarization_degree_isogeny_degree, hm1]
  exact ⟨hformula, hpullback, hbound, heq⟩

end Omega.DerivedConsequences
