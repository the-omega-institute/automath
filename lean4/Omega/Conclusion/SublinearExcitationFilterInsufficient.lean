import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The critical linear excitation slope from the spectral ratio `(ρ, η)`. -/
noncomputable def criticalExcitationSlope (rho eta : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log rho / Real.log (rho / eta)

/-- Concrete data for the conclusion-level contradiction: the excitation counts `k b` admit an
eventual upper bound below the critical slope, while every large-enough kernel-RH quotient must
satisfy the chapter's linear lower bound. -/
structure SublinearExcitationFilterData where
  rho : ℝ
  eta : ℝ
  hRho : 1 < rho
  hEta0 : 0 < eta
  hEtaLt : eta < rho
  k : ℕ → ℝ
  kernelRH : ℕ → Prop
  c : ℝ
  hSubcritical : c < criticalExcitationSlope rho eta
  hEventuallyUpper : ∃ N : ℕ, ∀ b ≥ N, k b ≤ c * b
  hNecessaryLower :
    ∀ b, 2 ≤ b → kernelRH b → criticalExcitationSlope rho eta * b ≤ k b

namespace SublinearExcitationFilterData

/-- Paper conclusion: beyond some finite order, the filtered quotients cannot keep satisfying
kernel RH. -/
def sublinearFiltersFailEventually (D : SublinearExcitationFilterData) : Prop :=
  ∃ N : ℕ, ∀ b ≥ N, ¬ D.kernelRH b

end SublinearExcitationFilterData

open SublinearExcitationFilterData

/-- Paper label: `thm:conclusion-sublinear-excitation-filter-insufficient`. -/
theorem paper_conclusion_sublinear_excitation_filter_insufficient
    (D : SublinearExcitationFilterData) : D.sublinearFiltersFailEventually := by
  rcases D.hEventuallyUpper with ⟨N, hN⟩
  refine ⟨max N 2, ?_⟩
  intro b hb hKernel
  have hbN : N ≤ b := le_trans (Nat.le_max_left _ _) hb
  have hb2 : 2 ≤ b := le_trans (Nat.le_max_right _ _) hb
  have hUpper : D.k b ≤ D.c * b := hN b hbN
  have hLower : criticalExcitationSlope D.rho D.eta * b ≤ D.k b :=
    D.hNecessaryLower b hb2 hKernel
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hb2
  have hStrict : D.c * b < criticalExcitationSlope D.rho D.eta * b := by
    exact mul_lt_mul_of_pos_right D.hSubcritical hbpos
  linarith

end Omega.Conclusion
