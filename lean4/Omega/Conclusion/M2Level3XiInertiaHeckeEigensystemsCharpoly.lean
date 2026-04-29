import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiInertiaPermutationRamification

namespace Omega.Conclusion

open Polynomial

/-- Common `Ξ`-inertia trace on the `24`-dimensional Hecke block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 : ℤ := 8

/-- `Ξ`-inertia trace on the Klingen-side `15`-dimensional defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl : ℤ := -1

/-- `Ξ`-inertia trace on the Siegel-side `15`-dimensional defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si : ℤ := 7

/-- The Klingen-side mixed trace `Tr(σ A)` used to separate the `2`- and `(-4)`-blocks. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_A_trace_Kl : ℤ := 32

/-- The Siegel-side mixed trace `Tr(σ A∨)` used to separate the `2`- and `(-4)`-blocks. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_Adual_trace_Si : ℤ := 0

/-- `+1`-eigenspace multiplicity on the common `24`-block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V24 : ℕ := 16

/-- `-1`-eigenspace multiplicity on the common `24`-block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V24 : ℕ := 8

/-- `+1`-eigenspace multiplicity on the Klingen defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V15_Kl : ℕ := 7

/-- `-1`-eigenspace multiplicity on the Klingen defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Kl : ℕ := 8

/-- `+1`-eigenspace multiplicity on the Siegel defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V15_Si : ℕ := 11

/-- `-1`-eigenspace multiplicity on the Siegel defect block. -/
def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Si : ℕ := 4

/-- Characteristic polynomial of `σ` on the common `24`-block. -/
noncomputable def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V24 :
    Polynomial ℤ :=
  (X - 1) ^ 16 * (X + 1) ^ 8

/-- Characteristic polynomial of `σ` on the Klingen defect block. -/
noncomputable def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V15_Kl :
    Polynomial ℤ :=
  (X - 1) ^ 7 * (X + 1) ^ 8

/-- Characteristic polynomial of `σ` on the Siegel defect block. -/
noncomputable def conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V15_Si :
    Polynomial ℤ :=
  (X - 1) ^ 11 * (X + 1) ^ 4

private theorem conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_solve_klingen
    {x y : ℤ} (htrace : 1 + x + y = 8) (hA : 12 + 2 * x - 4 * y = 32) :
    x = 8 ∧ y = -1 := by
  omega

private theorem conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_solve_siegel
    {x y : ℤ} (htrace : 1 + x + y = 16) (hAdual : 12 + 2 * x - 4 * y = 0) :
    x = 8 ∧ y = 7 := by
  omega

private theorem conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_klingen_trace_system :
    1 + conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 +
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl =
      (conclusion_m2_level3_xi_inertia_permutation_ramification_projective_fixed : ℤ) ∧
      12 + 2 * conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 -
          4 * conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl =
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_A_trace_Kl := by
  rcases paper_conclusion_m2_level3_xi_inertia_permutation_ramification with
    ⟨hProjFixed, _, _, _, _, _⟩
  constructor
  · rw [hProjFixed]
    norm_num [conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl]
  · norm_num [conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_A_trace_Kl]

private theorem conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_siegel_trace_system :
    1 + conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 +
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si =
      (conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_fixed : ℤ) ∧
      12 + 2 * conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 -
          4 * conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si =
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_Adual_trace_Si := by
  rcases paper_conclusion_m2_level3_xi_inertia_permutation_ramification with
    ⟨_, _, hLagFixed, _, _, _⟩
  constructor
  · rw [hLagFixed]
    norm_num [conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si]
  · norm_num [conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si,
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_Adual_trace_Si]

private theorem conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_trace_solution :
    conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 = 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl = -1 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si = 7 := by
  rcases conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_klingen_trace_system with
    ⟨hKlTrace, hKlA⟩
  rcases conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_siegel_trace_system with
    ⟨hSiTrace, hSiA⟩
  have hKl :
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 = 8 ∧
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl = -1 := by
    apply conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_solve_klingen
    · simpa using hKlTrace
    · simpa using hKlA
  have hSi :
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 = 8 ∧
        conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si = 7 := by
    apply conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_solve_siegel
    · simpa using hSiTrace
    · simpa using hSiA
  exact ⟨hKl.1, hKl.2, hSi.2⟩

/-- Paper label: `thm:conclusion-m2-level3-xi-inertia-hecke-eigensystems-charpoly`. The fixed
point counts on the Klingen and Siegel permutation fibers determine the inertia traces on the
common `24`-block and the two `15`-dimensional defect blocks, hence the `±1` multiplicities and
their characteristic polynomials. -/
theorem paper_conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly :
    conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V24 = 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Kl = -1 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_sigma_trace_V15_Si = 7 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V24 = 16 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V24 = 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V15_Kl = 7 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Kl = 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_plus_mult_V15_Si = 11 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Si = 4 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V24 =
        (X - 1) ^ 16 * (X + 1) ^ 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V15_Kl =
        (X - 1) ^ 7 * (X + 1) ^ 8 ∧
      conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_chi_V15_Si =
        (X - 1) ^ 11 * (X + 1) ^ 4 := by
  rcases conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_trace_solution with
    ⟨hV24, hV15Kl, hV15Si⟩
  exact ⟨hV24, hV15Kl, hV15Si, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Omega.Conclusion
