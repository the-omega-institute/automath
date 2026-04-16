import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Experiments.TVCertificateHist
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicTwoStateSFT

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Folding

/-- Alias exposing the metallic certificate objective on the `Omega.Folding` namespace path used by
paper-facing statements. -/
noncomputable abbrev metallicCertificateObjective : ℝ → ℝ :=
  MetallicParetoFrontier.metallicCertificateObjective

end Omega.Folding

namespace Omega.Experiments

private lemma metallicPerronRoot_one :
    Omega.Folding.metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
  rw [Omega.Folding.metallicPerronRoot, Real.goldenRatio]
  norm_num

private lemma metallicPerronRoot_nat_ge_goldenRatio (A : ℕ) (hA : 1 ≤ A) :
    Real.goldenRatio ≤ Omega.Folding.metallicPerronRoot (A : ℝ) := by
  have hA' : (1 : ℝ) ≤ A := by
    exact_mod_cast hA
  have hsqrt :
      Real.sqrt 5 ≤ Real.sqrt ((A : ℝ) ^ 2 + 4) := by
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [Omega.Folding.metallicPerronRoot, Real.goldenRatio]
  nlinarith

private lemma metallicPerronRoot_nat_eq_goldenRatio_iff (A : ℕ) (hA : 1 ≤ A) :
    Omega.Folding.metallicPerronRoot (A : ℝ) = Real.goldenRatio ↔ A = 1 := by
  constructor
  · intro h
    have hA' : (1 : ℝ) ≤ A := by
      exact_mod_cast hA
    have hsqrt :
        Real.sqrt 5 ≤ Real.sqrt ((A : ℝ) ^ 2 + 4) := by
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsum :
        ((A : ℝ) - 1) + (Real.sqrt ((A : ℝ) ^ 2 + 4) - Real.sqrt 5) = 0 := by
      rw [Omega.Folding.metallicPerronRoot, Real.goldenRatio] at h
      nlinarith
    have hAeq : (A : ℝ) = 1 := by
      have hA_nonneg : 0 ≤ (A : ℝ) - 1 := by linarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((A : ℝ) ^ 2 + 4) - Real.sqrt 5 := by linarith
      nlinarith
    exact_mod_cast hAeq
  · intro hA1
    subst hA1
    simpa using metallicPerronRoot_one

set_option maxHeartbeats 400000 in
/-- Among integer metallic-mean candidates `A ≥ 1`, the golden case `A = 1` uniquely minimizes
the TV-certificate constant because the certificate objective is strictly increasing in the
continuous Perron parameter and `λ_A` is minimized exactly at `A = 1`.
    cor:metallic-mean-golden-unique-optimal-tv-constant -/
theorem paper_metallic_mean_golden_unique_optimal_tv_constant :
    ∀ A : ℕ, 1 ≤ A →
      Omega.Folding.metallicCertificateObjective Real.goldenRatio ≤
        Omega.Folding.metallicCertificateObjective (Omega.Folding.metallicPerronRoot (A : ℝ)) ∧
      (Omega.Folding.metallicCertificateObjective (Omega.Folding.metallicPerronRoot (A : ℝ)) =
          Omega.Folding.metallicCertificateObjective Real.goldenRatio ↔
        A = 1) := by
  intro A hA
  let lam : ℝ := Omega.Folding.metallicPerronRoot (A : ℝ)
  have hphi_le : Real.goldenRatio ≤ lam := by
    simpa [lam] using metallicPerronRoot_nat_ge_goldenRatio A hA
  have hphi_lt : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hlam : lam ∈ Set.Ioi 1 := by
    show 1 < lam
    exact lt_of_lt_of_le hphi_lt hphi_le
  have hphi : Real.goldenRatio ∈ Set.Ioi 1 := Real.one_lt_goldenRatio
  have hle :
      Omega.Folding.metallicCertificateObjective Real.goldenRatio ≤
        Omega.Folding.metallicCertificateObjective lam := by
    by_cases hEq : Real.goldenRatio = lam
    · simpa [hEq]
    · have hlt : Real.goldenRatio < lam := lt_of_le_of_ne hphi_le hEq
      have hmono :
          Omega.Folding.metallicCertificateObjective Real.goldenRatio <
            Omega.Folding.metallicCertificateObjective lam := by
        simpa [Omega.Folding.metallicCertificateObjective] using
          metallicCertificateObjective_strictMonoOn hphi hlam hlt
      exact le_of_lt hmono
  refine ⟨hle, ?_⟩
  constructor
  · intro hEq
    by_cases hLam : lam = Real.goldenRatio
    · exact (metallicPerronRoot_nat_eq_goldenRatio_iff A hA).mp hLam
    · have hlt : Real.goldenRatio < lam := by
        refine lt_of_le_of_ne hphi_le ?_
        exact fun h => hLam h.symm
      have hmono :
          Omega.Folding.metallicCertificateObjective Real.goldenRatio <
            Omega.Folding.metallicCertificateObjective lam := by
        simpa [Omega.Folding.metallicCertificateObjective] using
          metallicCertificateObjective_strictMonoOn hphi hlam hlt
      rw [hEq] at hmono
      exact False.elim (lt_irrefl _ hmono)
  · intro hA1
    subst hA1
    simp [Omega.Folding.metallicCertificateObjective, metallicPerronRoot_one]

end Omega.Experiments
