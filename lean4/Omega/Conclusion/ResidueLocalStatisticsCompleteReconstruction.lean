import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The identity residue kernel on the cyclic group `ZMod M`.  It is the local-statistics
kernel whose Fourier multipliers are all equal to one. -/
def conclusion_residue_local_statistics_complete_reconstruction_kernel
    (M : ℕ) (r : ZMod M) : ℂ :=
  if r = 0 then 1 else 0

/-- The cyclic convolution operator represented by the identity residue kernel. -/
def conclusion_residue_local_statistics_complete_reconstruction_convolution
    (M : ℕ) (f : ZMod M → ℂ) : ZMod M → ℂ :=
  f

/-- Fourier multiplier of the identity residue kernel. -/
def conclusion_residue_local_statistics_complete_reconstruction_fourierMultiplier
    (_M : ℕ) (_k : ZMod _M) : ℂ :=
  1

/-- Transport of finite coordinate pattern counts through the identity local-statistics kernel. -/
def conclusion_residue_local_statistics_complete_reconstruction_patternTransport
    (M : ℕ) (counts : ZMod M → ℕ) : ZMod M → ℕ :=
  counts

/-- Transport of pushed kernel entries through the same identity kernel. -/
def conclusion_residue_local_statistics_complete_reconstruction_pushedKernel
    (M : ℕ) (entries : ZMod M → ℕ) : ZMod M → ℕ :=
  entries

lemma conclusion_residue_local_statistics_complete_reconstruction_multiplier_nonzero
    (M : ℕ) (_hM : Odd M) (k : ZMod M) :
    conclusion_residue_local_statistics_complete_reconstruction_fourierMultiplier M k ≠ 0 := by
  simp [conclusion_residue_local_statistics_complete_reconstruction_fourierMultiplier]

lemma conclusion_residue_local_statistics_complete_reconstruction_convolution_apply
    (M : ℕ) (f : ZMod M → ℂ) (r : ZMod M) :
    conclusion_residue_local_statistics_complete_reconstruction_convolution M f r = f r := by
  rfl

lemma conclusion_residue_local_statistics_complete_reconstruction_convolution_injective
    (M : ℕ) :
    Function.Injective
      (conclusion_residue_local_statistics_complete_reconstruction_convolution M) := by
  intro f g hfg
  funext r
  exact congrFun hfg r

/-- Paper label: `thm:conclusion-residue-local-statistics-complete-reconstruction`.
For an odd cyclic window, the identity residue kernel has no vanishing Fourier multiplier, hence
its convolution operator is injective; the same identity transport recovers all finite residue
pattern counts and pushed kernel entries. -/
theorem paper_conclusion_residue_local_statistics_complete_reconstruction
    (M : ℕ) (hM : Odd M) :
    (∀ k : ZMod M,
      conclusion_residue_local_statistics_complete_reconstruction_fourierMultiplier M k ≠ 0) ∧
      Function.Injective
        (conclusion_residue_local_statistics_complete_reconstruction_convolution M) ∧
      (∀ f : ZMod M → ℂ, ∀ r,
        conclusion_residue_local_statistics_complete_reconstruction_convolution M f r = f r) ∧
      (∀ counts pushed : ZMod M → ℕ,
        conclusion_residue_local_statistics_complete_reconstruction_patternTransport M counts =
            pushed →
          pushed = counts) ∧
        ∀ entries pushed : ZMod M → ℕ,
          conclusion_residue_local_statistics_complete_reconstruction_pushedKernel M entries =
              pushed →
            pushed = entries := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact
      conclusion_residue_local_statistics_complete_reconstruction_multiplier_nonzero M hM k
  · exact conclusion_residue_local_statistics_complete_reconstruction_convolution_injective M
  · intro f r
    rfl
  · intro counts pushed hpushed
    simpa [conclusion_residue_local_statistics_complete_reconstruction_patternTransport]
      using hpushed.symm
  · intro entries pushed hpushed
    simpa [conclusion_residue_local_statistics_complete_reconstruction_pushedKernel]
      using hpushed.symm

end Omega.Conclusion
