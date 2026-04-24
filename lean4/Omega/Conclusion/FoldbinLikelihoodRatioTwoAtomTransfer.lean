import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction

namespace Omega.Conclusion

noncomputable section

/-- The smaller limit likelihood-ratio value. -/
def foldbinLikelihoodRatioLow (q : ℕ) : ℝ :=
  1 / Real.goldenRatio ^ (q + 1)

/-- The larger limit likelihood-ratio value. -/
def foldbinLikelihoodRatioHigh (q : ℕ) : ℝ :=
  Real.goldenRatio ^ (q + 1)

/-- Reference-law weights for the two-atom likelihood-ratio limit. -/
def foldbinLikelihoodRatioReferenceLaw (q : ℕ) : Bool → ℝ
  | false => binfoldTwoPointLimitMassHigh Real.goldenRatio q
  | true => binfoldTwoPointLimitMassLow Real.goldenRatio q

/-- Transfer of a test function against the two-atom likelihood-ratio law. -/
def foldbinLikelihoodRatioExpectation (q : ℕ) (f : ℝ → ℝ) : ℝ :=
  foldbinLikelihoodRatioReferenceLaw q false * f (foldbinLikelihoodRatioLow q) +
    foldbinLikelihoodRatioReferenceLaw q true * f (foldbinLikelihoodRatioHigh q)

/-- Integer-order Rényi moments obtained by testing against monomials. -/
def foldbinLikelihoodRatioRenyiMoment (q α : ℕ) : ℝ :=
  foldbinLikelihoodRatioExpectation q (fun x => x ^ α)

/-- Paper-facing transfer package for the two-atom likelihood-ratio limit. -/
def FoldbinLikelihoodRatioTwoAtomTransferStatement : Prop :=
  ∀ q : ℕ,
    foldbinLikelihoodRatioLow q = 1 / Real.goldenRatio ^ (q + 1) ∧
      foldbinLikelihoodRatioHigh q = Real.goldenRatio ^ (q + 1) ∧
      foldbinLikelihoodRatioLow q ∈ Set.Icc (0 : ℝ) (foldbinLikelihoodRatioHigh q) ∧
      foldbinLikelihoodRatioHigh q ∈ Set.Icc (0 : ℝ) (foldbinLikelihoodRatioHigh q) ∧
      (∀ f : ℝ → ℝ,
        foldbinLikelihoodRatioExpectation q f =
          binfoldTwoPointLimitMassHigh Real.goldenRatio q * f (foldbinLikelihoodRatioLow q) +
            binfoldTwoPointLimitMassLow Real.goldenRatio q * f (foldbinLikelihoodRatioHigh q)) ∧
      (∀ α : ℕ,
        foldbinLikelihoodRatioRenyiMoment q α =
          binfoldTwoPointLimitMassHigh Real.goldenRatio q * (foldbinLikelihoodRatioLow q) ^ α +
            binfoldTwoPointLimitMassLow Real.goldenRatio q * (foldbinLikelihoodRatioHigh q) ^ α) ∧
      foldbinLikelihoodRatioRenyiMoment q 1 = 1

private theorem foldbinLikelihoodRatioLow_mem_interval (q : ℕ) :
    foldbinLikelihoodRatioLow q ∈ Set.Icc (0 : ℝ) (foldbinLikelihoodRatioHigh q) := by
  let x : ℝ := Real.goldenRatio ^ (q + 1)
  have hxge : (1 : ℝ) ≤ x := by
    dsimp [x]
    simpa using
      (one_le_pow₀ (n := q + 1) (a := Real.goldenRatio) (le_of_lt Real.one_lt_goldenRatio))
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hupper : 1 / x ≤ x := by
    have hx2 : (1 : ℝ) ≤ x * x := by nlinarith
    exact (div_le_iff₀ hxpos).2 (by simpa using hx2)
  rw [foldbinLikelihoodRatioLow, foldbinLikelihoodRatioHigh]
  constructor
  · positivity
  · simpa [x] using hupper

private theorem foldbinLikelihoodRatioRenyiAtOne (q : ℕ) :
    foldbinLikelihoodRatioRenyiMoment q 1 = 1 := by
  let x : ℝ := Real.goldenRatio ^ (q + 1)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hlow : binfoldTwoPointLimitMassLow Real.goldenRatio q = 1 / (1 + x) := by
    simpa [x] using (binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).1
  have hhigh : binfoldTwoPointLimitMassHigh Real.goldenRatio q = x / (1 + x) := by
    simpa [x] using (binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).2
  unfold foldbinLikelihoodRatioRenyiMoment foldbinLikelihoodRatioExpectation
    foldbinLikelihoodRatioReferenceLaw foldbinLikelihoodRatioLow foldbinLikelihoodRatioHigh
  rw [hlow, hhigh]
  field_simp [hxpos.ne']
  ring

/-- Paper label: `thm:conclusion-foldbin-likelihood-ratio-two-atom-transfer`. The two-atom foldbin
asymptotic identifies the limiting likelihood-ratio values and their weights, confines them to a
fixed compact interval, transfers every test function to the limiting two-atom law, and in
particular yields the closed Rényi moments with the `α = 1` normalization. -/
theorem paper_conclusion_foldbin_likelihood_ratio_two_atom_transfer :
    FoldbinLikelihoodRatioTwoAtomTransferStatement := by
  intro q
  refine ⟨rfl, rfl, foldbinLikelihoodRatioLow_mem_interval q, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, le_rfl⟩
    unfold foldbinLikelihoodRatioHigh
    positivity
  · intro f
    rfl
  · intro α
    rfl
  · exact foldbinLikelihoodRatioRenyiAtOne q

end

end Omega.Conclusion
