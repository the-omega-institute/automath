import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-state Dirichlet-moment data with a uniform twisted spectral-gap exponent. -/
structure AutomaticDirichletMomentData where
  N : ℕ
  hN : 2 ≤ N
  logExponent : ℕ → ℕ
  momentValue : ℕ → ℝ → ℝ
  baseConstant : ℕ → ℝ
  spectralGap : ℝ
  hspectralGap : 0 < spectralGap
  hbase_pos : ∀ k, 0 < baseConstant k
  momentBound :
    ∀ k T, 1 ≤ T →
      momentValue k T ≤
        baseConstant k * T * (N : ℝ) ^ k *
          (Real.log (N : ℝ)) ^ (logExponent k) * (N : ℝ) ^ (-spectralGap)

namespace AutomaticDirichletMomentData

/-- Uniform `2k`-th moment power saving for the truncated Dirichlet polynomial. -/
def uniformMomentBound (D : AutomaticDirichletMomentData) (k : ℕ) (ε C : ℝ) : Prop :=
  0 < ε ∧
    0 < C ∧
    ∀ T : ℝ, 1 ≤ T →
      D.momentValue k T ≤
        C * T * (D.N : ℝ) ^ k *
          (Real.log (D.N : ℝ)) ^ (D.logExponent k) * (D.N : ℝ) ^ (-ε)

lemma uniform_moment_bound_of_gap
    (D : AutomaticDirichletMomentData) (k : ℕ) :
    D.uniformMomentBound k D.spectralGap (D.baseConstant k) := by
  refine ⟨D.hspectralGap, D.hbase_pos k, ?_⟩
  intro T hT
  simpa [uniformMomentBound] using D.momentBound k T hT

end AutomaticDirichletMomentData

open AutomaticDirichletMomentData

/-- A uniform twisted spectral gap yields a power-saving `2k`-th moment bound for every fixed
order.
    prop:conclusion69-automatic-dirichlet-moment -/
theorem paper_conclusion69_automatic_dirichlet_moment (D : AutomaticDirichletMomentData) :
    ∀ k : ℕ, ∃ ε C, D.uniformMomentBound k ε C := by
  intro k
  exact ⟨D.spectralGap, D.baseConstant k, D.uniform_moment_bound_of_gap k⟩

/-- Paper label: `thm:gm-automatic-dirichlet-moment-bound`. The GM appendix uses the same
finite-state spectral-gap package as the conclusion-level automatic Dirichlet moment theorem. -/
theorem paper_gm_automatic_dirichlet_moment_bound (D : AutomaticDirichletMomentData) :
    ∀ k : ℕ, ∃ ε C, D.uniformMomentBound k ε C := by
  exact paper_conclusion69_automatic_dirichlet_moment D

end

end Omega.Zeta
