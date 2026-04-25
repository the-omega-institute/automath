import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FoldbinLikelihoodRatioTwoAtomTransfer
import Omega.GU.TimeUnitLogphiProtocol

namespace Omega.Conclusion

open Filter Topology

noncomputable section

/-- The conclusion-level Renyi entropy clock; every order reads the same exponential scale. -/
def conclusion_binfold_renyi_exponential_blindness_entropy (_alpha t : ℕ) : ℝ :=
  Omega.GU.entropyTime t

/-- Deviation of the transferred two-atom likelihood-ratio law from the uniform baseline
normalization. -/
def conclusion_binfold_renyi_exponential_blindness_uniform_defect (_alpha q : ℕ) : ℝ :=
  |foldbinLikelihoodRatioRenyiMoment q 1 - 1|

/-- Paper label: `cor:conclusion-binfold-renyi-exponential-blindness`.
Every Renyi order inherits the same `log φ` entropy slope from the golden entropy clock, while the
transported two-atom likelihood-ratio law stays uniformly blind to the baseline at order `1`,
hence the associated baseline defect is bounded independently of the resolution level. -/
theorem paper_conclusion_binfold_renyi_exponential_blindness :
    (∀ alpha : ℕ,
      Tendsto (fun t => conclusion_binfold_renyi_exponential_blindness_entropy alpha t / (t : ℝ))
        atTop (𝓝 (Real.log Real.goldenRatio))) ∧
      (∀ alpha q : ℕ,
        conclusion_binfold_renyi_exponential_blindness_uniform_defect alpha q = 0) ∧
      (∀ alpha q : ℕ,
        conclusion_binfold_renyi_exponential_blindness_uniform_defect alpha q ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro alpha
    simpa [conclusion_binfold_renyi_exponential_blindness_entropy] using
      Omega.GU.paper_terminal_tau_corr_logphi.1
  · intro alpha q
    have hTransfer := paper_conclusion_foldbin_likelihood_ratio_two_atom_transfer q
    rcases hTransfer with ⟨_, _, _, _, _, _, hOne⟩
    simp [conclusion_binfold_renyi_exponential_blindness_uniform_defect, hOne]
  · intro alpha q
    have hZero :
        conclusion_binfold_renyi_exponential_blindness_uniform_defect alpha q = 0 := by
      have hTransfer := paper_conclusion_foldbin_likelihood_ratio_two_atom_transfer q
      rcases hTransfer with ⟨_, _, _, _, _, _, hOne⟩
      simp [conclusion_binfold_renyi_exponential_blindness_uniform_defect, hOne]
    rw [hZero]
    norm_num

end

end Omega.Conclusion
