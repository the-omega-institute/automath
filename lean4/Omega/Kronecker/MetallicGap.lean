import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicTwoStateSFT

open Omega.Folding
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Kronecker

private lemma metallicPerronRoot_strictMonoOn :
    StrictMonoOn metallicPerronRoot (Set.Ici 1) := by
  intro A₁ hA₁ A₂ hA₂ hlt
  have hA₁' : 1 ≤ A₁ := hA₁
  have hA₂' : 1 ≤ A₂ := hA₂
  have hsq : A₁ ^ 2 + 4 < A₂ ^ 2 + 4 := by
    nlinarith
  have hsqrt : Real.sqrt (A₁ ^ 2 + 4) < Real.sqrt (A₂ ^ 2 + 4) := by
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  rw [metallicPerronRoot, metallicPerronRoot]
  nlinarith

private lemma metallicPerronRoot_gt_one {A : Real} (hA : 1 ≤ A) :
    1 < metallicPerronRoot A := by
  have hsq : (2 : Real) ^ 2 < A ^ 2 + 4 := by
    nlinarith [sq_nonneg A]
  have hsqrt : 2 < Real.sqrt (A ^ 2 + 4) := by
    have h' : Real.sqrt ((2 : Real) ^ 2) < Real.sqrt (A ^ 2 + 4) := by
      exact Real.sqrt_lt_sqrt (by positivity) hsq
    simpa using h'
  rw [metallicPerronRoot]
  nlinarith

private lemma metallicPerronRoot_sub_inv_eq (A : Real) (hA : 1 ≤ A) :
    metallicPerronRoot A - (metallicPerronRoot A)⁻¹ = A := by
  let lam : Real := metallicPerronRoot A
  have hlam_pos : 0 < lam := by
    simpa [lam] using metallicPerronRoot_pos hA
  have hlam_ne : lam ≠ 0 := hlam_pos.ne'
  have hquad : lam ^ 2 - A * lam - 1 = 0 := by
    simpa [lam] using metallicPerronRoot_quadratic A
  have hzero : lam - A - lam⁻¹ = 0 := by
    have hrew : lam - A - lam⁻¹ = (lam ^ 2 - A * lam - 1) / lam := by
      field_simp [hlam_ne]
    rw [hrew, hquad]
    simp
  linarith

/-- The metallic certificate coefficient `κ(A) = A / log λ_A` is strictly
increasing on the constant-type branch `A ≥ 1`, so the golden case `A = 1`
is the unique left endpoint minimizer.
    thm:metallic-gap -/
theorem paper_kronecker_metallic_gap :
    StrictMonoOn (fun A : Real => A / Real.log (metallicPerronRoot A)) (Set.Ici 1) := by
  intro A₁ hA₁ A₂ hA₂ hlt
  have hA₁' : 1 ≤ A₁ := hA₁
  have hA₂' : 1 ≤ A₂ := hA₂
  have hlam₁ : metallicPerronRoot A₁ ∈ Set.Ioi 1 := metallicPerronRoot_gt_one hA₁'
  have hlam₂ : metallicPerronRoot A₂ ∈ Set.Ioi 1 := metallicPerronRoot_gt_one hA₂'
  have hlam_lt : metallicPerronRoot A₁ < metallicPerronRoot A₂ :=
    metallicPerronRoot_strictMonoOn hA₁ hA₂ hlt
  calc
    A₁ / Real.log (metallicPerronRoot A₁)
        = metallicCertificateObjective (metallicPerronRoot A₁) := by
            nth_rewrite 1 [show A₁ = metallicPerronRoot A₁ - (metallicPerronRoot A₁)⁻¹ by
              simpa using (metallicPerronRoot_sub_inv_eq A₁ hA₁').symm]
            rw [metallicCertificateObjective]
    _ < metallicCertificateObjective (metallicPerronRoot A₂) := by
          exact metallicCertificateObjective_strictMonoOn hlam₁ hlam₂ hlam_lt
    _ = A₂ / Real.log (metallicPerronRoot A₂) := by
          rw [metallicCertificateObjective]
          rw [metallicPerronRoot_sub_inv_eq A₂ hA₂']

end Omega.Kronecker
