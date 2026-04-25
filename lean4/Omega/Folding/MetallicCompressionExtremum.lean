import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicCompressionLockingLambda2
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicTwoStateSFT

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

/-!
# One-sided monotonicity seed for metallic compression

This file records the paper-facing seed/package wrapper for
`prop:metallic-compression-extremum`.
-/

namespace Omega.Folding.MetallicCompressionExtremum

private lemma metallic_compression_extremum_metallicPerronRoot_strictMonoOn :
    StrictMonoOn Omega.Folding.metallicPerronRoot (Set.Ici 1) := by
  intro A₁ hA₁ A₂ hA₂ hlt
  have hA₁_nonneg : 0 ≤ A₁ := le_trans (by norm_num) hA₁
  have hA₂_nonneg : 0 ≤ A₂ := le_trans (by norm_num) hA₂
  have hsq : A₁ ^ 2 + 4 < A₂ ^ 2 + 4 := by
    nlinarith
  have hsqrt : Real.sqrt (A₁ ^ 2 + 4) < Real.sqrt (A₂ ^ 2 + 4) := by
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  rw [Omega.Folding.metallicPerronRoot, Omega.Folding.metallicPerronRoot]
  nlinarith

private lemma metallic_compression_extremum_metallicPerronRoot_one :
    Omega.Folding.metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
  rw [Omega.Folding.metallicPerronRoot, Real.goldenRatio]
  norm_num

private lemma metallic_compression_extremum_metallicPerronRoot_two :
    Omega.Folding.metallicPerronRoot (2 : ℝ) = 1 + Real.sqrt 2 := by
  rw [Omega.Folding.metallicPerronRoot]
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 2 + 4) = 2 * Real.sqrt 2 := by
    rw [show ((2 : ℝ) ^ 2 + 4) = (2 * Real.sqrt 2) ^ 2 by
      have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [hsqrt2_sq]]
    rw [Real.sqrt_sq]
    positivity
  rw [hsqrt]
  ring

private lemma metallic_compression_extremum_metallicPerronRoot_sub_inv_eq (A : ℝ) (hA : 1 ≤ A) :
    Omega.Folding.metallicPerronRoot A - (Omega.Folding.metallicPerronRoot A)⁻¹ = A := by
  let lam : ℝ := Omega.Folding.metallicPerronRoot A
  have hlam_pos : 0 < lam := by
    simpa [lam] using Omega.Folding.metallicPerronRoot_pos hA
  have hlam_ne : lam ≠ 0 := hlam_pos.ne'
  have hquad : lam ^ 2 - A * lam - 1 = 0 := by
    simpa [lam] using Omega.Folding.metallicPerronRoot_quadratic A
  have hzero : lam - A - lam⁻¹ = 0 := by
    have hrew : lam - A - lam⁻¹ = (lam ^ 2 - A * lam - 1) / lam := by
      field_simp [hlam_ne]
    rw [hrew, hquad]
    simp
  linarith

private lemma metallic_compression_extremum_log_eq_objective {A : ℝ} (hA : 1 ≤ A) :
    Real.log ((A + 1) / Omega.Folding.metallicPerronRoot A) =
      metallicCompressionObjective (Omega.Folding.metallicPerronRoot A) := by
  let lam : ℝ := Omega.Folding.metallicPerronRoot A
  have hlam_pos : 0 < lam := by
    simpa [lam] using Omega.Folding.metallicPerronRoot_pos hA
  have hAeq : A = lam - lam⁻¹ := by
    simpa [lam] using
      (metallic_compression_extremum_metallicPerronRoot_sub_inv_eq A hA).symm
  calc
    Real.log ((A + 1) / Omega.Folding.metallicPerronRoot A)
        = Real.log ((A + 1) / lam) := by rfl
    _ = Real.log (((lam - lam⁻¹) + 1) / lam) := by rw [hAeq]
    _ = Real.log (1 + lam⁻¹ - lam⁻¹ ^ 2) := by
          congr 1
          field_simp [hlam_pos.ne']
          ring
    _ = metallicCompressionObjective lam := by rw [metallicCompressionObjective]
    _ = metallicCompressionObjective (Omega.Folding.metallicPerronRoot A) := by
          simp [lam]

private lemma metallic_compression_extremum_rhs_eq_objective_two :
    Real.log (((3 / 2 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (3 / 2)) =
      metallicCompressionObjective (2 : ℝ) := by
  rcases Omega.Folding.paper_metallic_compression_locking_lambda2 with ⟨hroot, _⟩
  calc
    Real.log (((3 / 2 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (3 / 2))
        = Real.log (((3 / 2 : ℝ) + 1) / 2) := by rw [hroot]
    _ = Real.log (5 / 4 : ℝ) := by norm_num
    _ = metallicCompressionObjective (2 : ℝ) := by
          rw [metallicCompressionObjective]
          norm_num

private lemma metallic_compression_extremum_lam_ge_phi {A : ℝ} (hA : 1 ≤ A) :
    Real.goldenRatio ≤ Omega.Folding.metallicPerronRoot A := by
  rcases lt_or_eq_of_le hA with hlt | rfl
  · exact le_of_lt <|
      (by
        simpa [metallic_compression_extremum_metallicPerronRoot_one] using
          (metallic_compression_extremum_metallicPerronRoot_strictMonoOn
            (by norm_num : (1 : ℝ) ∈ Set.Ici 1) hA hlt))
  · simpa [metallic_compression_extremum_metallicPerronRoot_one]

private lemma metallic_compression_extremum_inside_lt_two {A : ℝ} (hA : 1 ≤ A) (hLt : A < 3 / 2) :
    Omega.Folding.metallicPerronRoot A < 2 := by
  have hroot :
      Omega.Folding.metallicPerronRoot (3 / 2 : ℝ) = 2 :=
    Omega.Folding.paper_metallic_compression_locking_lambda2.1
  have hlt_root :=
    metallic_compression_extremum_metallicPerronRoot_strictMonoOn
      hA (by norm_num : (3 / 2 : ℝ) ∈ Set.Ici 1) hLt
  simpa [hroot] using hlt_root

private lemma metallic_compression_extremum_two_lt_inside {A : ℝ} (hGt : 3 / 2 < A) :
    2 < Omega.Folding.metallicPerronRoot A := by
  have hroot :
      Omega.Folding.metallicPerronRoot (3 / 2 : ℝ) = 2 :=
    Omega.Folding.paper_metallic_compression_locking_lambda2.1
  have hlt_root :=
    metallic_compression_extremum_metallicPerronRoot_strictMonoOn
      (by norm_num : (3 / 2 : ℝ) ∈ Set.Ici 1) (by
        show 1 ≤ A
        linarith) hGt
  simpa [hroot] using hlt_root

private lemma metallic_compression_extremum_inside_diff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (1 + y⁻¹ - y⁻¹ ^ 2) - (1 + x⁻¹ - x⁻¹ ^ 2) =
      (x - y) * (x * y - x - y) / (x ^ 2 * y ^ 2) := by
  field_simp [hx, hy]
  ring

private lemma metallic_compression_extremum_objective_strictAntiOn_Ioi_two :
    StrictAntiOn metallicCompressionObjective (Set.Ioi 2) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hx1 : 1 < x := lt_trans (by norm_num) hx
  have hy1 : 1 < y := lt_trans (by norm_num) hy
  have hprod : 0 < x * y - x - y := by
    have hx2 : 0 < x - 2 := sub_pos.mpr hx
    have hy2 : 0 < y - 2 := sub_pos.mpr hy
    have hrew : x * y - x - y = (x - 2) * (y - 2) + (x - 2) + (y - 2) := by
      ring
    rw [hrew]
    positivity
  have hfrac :
      (x - y) * (x * y - x - y) / (x ^ 2 * y ^ 2) < 0 := by
    have hnum : (x - y) * (x * y - x - y) < 0 := by
      have hxy' : x - y < 0 := sub_neg.mpr hxy
      exact mul_neg_of_neg_of_pos hxy' hprod
    have hden : 0 < x ^ 2 * y ^ 2 := by positivity
    exact div_neg_of_neg_of_pos hnum hden
  have hinside :
      1 + y⁻¹ - y⁻¹ ^ 2 < 1 + x⁻¹ - x⁻¹ ^ 2 := by
    have hdiff := metallic_compression_extremum_inside_diff hx0.ne' hy0.ne'
    linarith
  have hposy : 0 < 1 + y⁻¹ - y⁻¹ ^ 2 := metallicCompressionInside_pos (le_of_lt hy1)
  simpa [metallicCompressionObjective] using Real.log_lt_log hposy hinside

private lemma metallic_compression_extremum_one_add_sqrt_two_lt_three :
    1 + Real.sqrt 2 < (3 : ℝ) := by
  have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [hsqrt2_sq]

private lemma metallic_compression_extremum_metallicPerronRoot_two_lt_nat {A : ℕ} (hA : 3 ≤ A) :
    Omega.Folding.metallicPerronRoot (2 : ℝ) < Omega.Folding.metallicPerronRoot (A : ℝ) := by
  have hAreal : (3 : ℝ) ≤ A := by exact_mod_cast hA
  calc
    Omega.Folding.metallicPerronRoot (2 : ℝ) = 1 + Real.sqrt 2 :=
      metallic_compression_extremum_metallicPerronRoot_two
    _ < 3 := metallic_compression_extremum_one_add_sqrt_two_lt_three
    _ ≤ A := hAreal
    _ < Omega.Folding.metallicPerronRoot (A : ℝ) := by
          have hApos : (0 : ℝ) < A := by positivity
          rw [Omega.Folding.metallicPerronRoot]
          have hsqrt : (A : ℝ) < Real.sqrt ((A : ℝ) ^ 2 + 4) := by
            have h' : Real.sqrt ((A : ℝ) ^ 2) < Real.sqrt ((A : ℝ) ^ 2 + 4) := by
              exact Real.sqrt_lt_sqrt (sq_nonneg (A : ℝ)) (by nlinarith)
            simpa [Real.sqrt_sq (le_of_lt hApos)] using h'
          nlinarith

private lemma metallic_compression_extremum_objective_one_lt_two :
    Real.log (((1 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (1 : ℝ)) <
      Real.log ((3 : ℝ) / Omega.Folding.metallicPerronRoot (2 : ℝ)) := by
  rw [metallic_compression_extremum_metallicPerronRoot_one,
    metallic_compression_extremum_metallicPerronRoot_two]
  have hleft_pos : 0 < 2 / Real.goldenRatio := by positivity
  have hineq : 2 / Real.goldenRatio < 3 / (1 + Real.sqrt 2) := by
    change 2 / ((1 + Real.sqrt 5) / 2) < 3 / (1 + Real.sqrt 2)
    have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      positivity
    have hphi_ne : ((1 + Real.sqrt 5) / 2 : ℝ) ≠ 0 := by positivity
    have hsqrt2_ne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    field_simp [hphi_ne, hsqrt2_ne]
    have hsq : (1 + 4 * Real.sqrt 2) ^ 2 < (3 * Real.sqrt 5) ^ 2 := by
      nlinarith [hsqrt2_sq, hsqrt5_sq]
    have hmain : 1 + 4 * Real.sqrt 2 < 3 * Real.sqrt 5 := by
      have hleft_nonneg : 0 ≤ 1 + 4 * Real.sqrt 2 := by positivity
      have hright_nonneg : 0 ≤ 3 * Real.sqrt 5 := by positivity
      nlinarith [hsq, hleft_nonneg, hright_nonneg]
    nlinarith [hmain]
  have hleft_pos' : 0 < ((1 : ℝ) + 1) / Real.goldenRatio := by positivity
  have hineq' : ((1 : ℝ) + 1) / Real.goldenRatio < 3 / (1 + Real.sqrt 2) := by
    convert hineq using 1 <;> ring
  exact Real.log_lt_log hleft_pos' hineq'

/-- Paper seed for the large-`A` side of the metallic-compression extremum:
    once `A > 3 / 2`, the metallic eigenvalue term lies strictly below `A + 1`.
    prop:metallic-compression-extremum -/
theorem paper_metallic_compression_extremum_seeds {A : ℝ} (hA : 3 / 2 < A) :
    (A + Real.sqrt (A^2 + 4)) / 2 < A + 1 := by
  have hA_pos : 0 < A := by nlinarith
  have hA2_nonneg : 0 ≤ A + 2 := by linarith
  have hsq : A ^ 2 + 4 < (A + 2) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (A ^ 2 + 4) < A + 2 := by
    have h' : Real.sqrt (A ^ 2 + 4) < Real.sqrt ((A + 2) ^ 2) := by
      exact Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg A]) hsq
    simpa [Real.sqrt_sq hA2_nonneg] using h'
  nlinarith

/-- Packaged form of the metallic-compression extremum seed.
    prop:metallic-compression-extremum -/
theorem paper_metallic_compression_extremum_package {A : ℝ} (hA : 3 / 2 < A) :
    (A + Real.sqrt (A^2 + 4)) / 2 < A + 1 :=
  paper_metallic_compression_extremum_seeds hA

set_option maxHeartbeats 400000 in
/-- At the metallic-compression extremum `A = 3 / 2`, the Perron root locks to `2`, and the
    compression slope takes the closed form `log (5 / 4)`.
    cor:metallic-compression-locking-lambda2 -/
theorem paper_metallic_compression_locking_lambda2 :
    ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2 = 2 ∧
      Real.log (((3 / 2 : ℝ) + 1) / (((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2)) =
        Real.log (5 / 4) := by
  have hsqrt : Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4) = 5 / 2 := by
    have hnonneg : (0 : ℝ) ≤ 5 / 2 := by positivity
    rw [show (((3 / 2 : ℝ) ^ 2) + 4) = (5 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq hnonneg]
  have hlambda : ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2 = 2 := by
    calc
      ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2
          = ((3 / 2 : ℝ) + 5 / 2) / 2 := by rw [hsqrt]
      _ = 2 := by norm_num
  constructor
  · exact hlambda
  · calc
      Real.log (((3 / 2 : ℝ) + 1) / (((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2))
          = Real.log (((3 / 2 : ℝ) + 1) / 2) := by rw [hlambda]
      _ = Real.log (5 / 4) := by norm_num

/-- The metallic compression objective is uniquely maximized at `A = 3/2` on `[1, ∞)`, and
    among integers `A ≥ 1` its maximum is attained at `A = 2`.
    prop:metallic-compression-extremum -/
theorem paper_metallic_compression_extremum :
    (∀ {A : ℝ}, 1 ≤ A → A ≠ 3 / 2 →
      Real.log ((A + 1) / Omega.Folding.metallicPerronRoot A) <
        Real.log (((3 / 2 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (3 / 2))) ∧
    (∀ A : ℕ, 1 ≤ A →
      Real.log (((A : ℝ) + 1) / Omega.Folding.metallicPerronRoot (A : ℝ)) ≤
        Real.log ((3 : ℝ) / Omega.Folding.metallicPerronRoot (2 : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro A hA hA_ne
    have hphi : Real.goldenRatio ≤ Omega.Folding.metallicPerronRoot A :=
      metallic_compression_extremum_lam_ge_phi hA
    have hlogeq :
        Real.log ((A + 1) / Omega.Folding.metallicPerronRoot A) =
          metallicCompressionObjective (Omega.Folding.metallicPerronRoot A) :=
      metallic_compression_extremum_log_eq_objective hA
    have hright :
        Real.log (((3 / 2 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (3 / 2)) =
          metallicCompressionObjective (2 : ℝ) :=
      metallic_compression_extremum_rhs_eq_objective_two
    rcases paper_metallic_pareto_frontier_lambda with ⟨_, hgt, hinterval⟩
    rcases lt_or_gt_of_ne hA_ne with hlt | hgtA
    · have hlam_lt_two : Omega.Folding.metallicPerronRoot A < 2 :=
        metallic_compression_extremum_inside_lt_two hA hlt
      have hcomp :
          metallicCompressionObjective (Omega.Folding.metallicPerronRoot A) <
            metallicCompressionObjective (2 : ℝ) := by
        exact (hinterval ⟨hphi, le_of_lt hlam_lt_two⟩
          ⟨le_of_lt Real.goldenRatio_lt_two, le_rfl⟩ hlam_lt_two).1
      simpa [hlogeq, hright] using hcomp
    · have hlam_gt_two : 2 < Omega.Folding.metallicPerronRoot A :=
        metallic_compression_extremum_two_lt_inside hgtA
      have hcomp :
          metallicCompressionObjective (Omega.Folding.metallicPerronRoot A) <
            metallicCompressionObjective (2 : ℝ) := (hgt hlam_gt_two).1
      simpa [hlogeq, hright] using hcomp
  · intro A hA
    by_cases hA1 : A = 1
    · subst hA1
      simpa using le_of_lt metallic_compression_extremum_objective_one_lt_two
    by_cases hA2 : A = 2
    · subst hA2
      exact le_of_eq (by congr 1; norm_num)
    · have hA3 : 3 ≤ A := by omega
      have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hleft :
          Real.log (((A : ℝ) + 1) / Omega.Folding.metallicPerronRoot (A : ℝ)) =
            metallicCompressionObjective (Omega.Folding.metallicPerronRoot (A : ℝ)) :=
        metallic_compression_extremum_log_eq_objective hAreal
      have hright :
          Real.log ((3 : ℝ) / Omega.Folding.metallicPerronRoot (2 : ℝ)) =
            metallicCompressionObjective (Omega.Folding.metallicPerronRoot (2 : ℝ)) :=
        by
          calc
            Real.log ((3 : ℝ) / Omega.Folding.metallicPerronRoot (2 : ℝ))
                = Real.log (((2 : ℝ) + 1) / Omega.Folding.metallicPerronRoot (2 : ℝ)) := by
                    congr 1
                    norm_num
            _ = metallicCompressionObjective (Omega.Folding.metallicPerronRoot (2 : ℝ)) :=
                  metallic_compression_extremum_log_eq_objective (A := (2 : ℝ)) (by norm_num)
      have hroot_lt :
          Omega.Folding.metallicPerronRoot (2 : ℝ) <
            Omega.Folding.metallicPerronRoot (A : ℝ) :=
        metallic_compression_extremum_metallicPerronRoot_two_lt_nat hA3
      have hroot_two_mem : Omega.Folding.metallicPerronRoot (2 : ℝ) ∈ Set.Ioi 2 := by
        rw [metallic_compression_extremum_metallicPerronRoot_two]
        have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
          simpa [Real.sqrt_one] using
            (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
        have htwo_lt : (2 : ℝ) < 1 + Real.sqrt 2 := by
          nlinarith
        simpa using htwo_lt
      have hroot_A_mem : Omega.Folding.metallicPerronRoot (A : ℝ) ∈ Set.Ioi 2 := by
        exact lt_trans hroot_two_mem hroot_lt
      have hcomp :
          metallicCompressionObjective (Omega.Folding.metallicPerronRoot (A : ℝ)) <
            metallicCompressionObjective (Omega.Folding.metallicPerronRoot (2 : ℝ)) := by
        exact metallic_compression_extremum_objective_strictAntiOn_Ioi_two
          hroot_two_mem hroot_A_mem hroot_lt
      exact le_of_lt (by simpa [hleft, hright] using hcomp)

end Omega.Folding.MetallicCompressionExtremum
