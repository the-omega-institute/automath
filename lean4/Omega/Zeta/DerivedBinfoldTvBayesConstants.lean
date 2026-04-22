import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction
import Omega.Zeta.XiTimePart9odEscortTvCollapseBlockUniform

namespace Omega.Zeta

noncomputable section

/-- The golden two-atom limit law coming from the verified binfold reconstruction. -/
def derivedBinfoldLimitLaw (q : ℕ) : Bool → ℝ
  | false => Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q
  | true => Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q

/-- The companion law with the two atoms swapped. -/
def derivedBinfoldSwappedLaw (q : ℕ) : Bool → ℝ
  | false => Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q
  | true => Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q

/-- The two-point total-variation distance is one half of the `ℓ¹` distance. -/
def derivedBinfoldTv (q : ℕ) : ℝ :=
  xiEscortTvDistance (derivedBinfoldLimitLaw q) (derivedBinfoldSwappedLaw q)

/-- Equal-prior Bayes error read off from the total-variation distance. -/
def derivedBinfoldBayesError (q : ℕ) : ℝ :=
  (1 - derivedBinfoldTv q) / 2

/-- The audited exponential error term is unchanged. -/
def derivedBinfoldErrorTerm (m : ℕ) : ℝ :=
  xiEscortCollapseRate m

/-- Paper-facing package of the explicit masses, the TV/Bayes identities, and the unchanged
exponential error term. -/
def DerivedBinfoldTvBayesConstantsStatement : Prop :=
  (∀ q : ℕ,
    derivedBinfoldLimitLaw q false = 1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
      derivedBinfoldLimitLaw q true =
        Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) ∧
      derivedBinfoldTv q =
        (|derivedBinfoldLimitLaw q false - derivedBinfoldSwappedLaw q false| +
            |derivedBinfoldLimitLaw q true - derivedBinfoldSwappedLaw q true|) / 2 ∧
      derivedBinfoldBayesError q = (1 - derivedBinfoldTv q) / 2 ∧
      derivedBinfoldBayesError q = 1 / (1 + Real.goldenRatio ^ (q + 1))) ∧
    ∀ m : ℕ, derivedBinfoldErrorTerm m = xiEscortCollapseRate m

private theorem derivedBinfoldMassLow_closed (q : ℕ) :
    derivedBinfoldLimitLaw q false = 1 / (1 + Real.goldenRatio ^ (q + 1)) := by
  simpa [derivedBinfoldLimitLaw] using
    (Omega.Conclusion.binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).1

private theorem derivedBinfoldMassHigh_closed (q : ℕ) :
    derivedBinfoldLimitLaw q true = Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) := by
  simpa [derivedBinfoldLimitLaw] using
    (Omega.Conclusion.binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).2

private theorem derivedBinfoldLow_le_high (q : ℕ) :
    derivedBinfoldLimitLaw q false ≤ derivedBinfoldLimitLaw q true := by
  rw [derivedBinfoldMassLow_closed, derivedBinfoldMassHigh_closed]
  have hpow_ge : (1 : ℝ) ≤ Real.goldenRatio ^ (q + 1) := by
    simpa using
      (one_le_pow₀ (n := q + 1) (a := Real.goldenRatio) (le_of_lt Real.one_lt_goldenRatio))
  have hden_nonneg : 0 ≤ 1 + Real.goldenRatio ^ (q + 1) := by
    positivity
  exact div_le_div_of_nonneg_right hpow_ge hden_nonneg

private theorem derivedBinfoldTv_closed (q : ℕ) :
    derivedBinfoldTv q = derivedBinfoldLimitLaw q true - derivedBinfoldLimitLaw q false := by
  have hle : derivedBinfoldLimitLaw q false ≤ derivedBinfoldLimitLaw q true :=
    derivedBinfoldLow_le_high q
  have hcore :
      Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q ≤
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q := by
    simpa [derivedBinfoldLimitLaw] using hle
  have habs₁ :
      |derivedBinfoldLimitLaw q false - derivedBinfoldSwappedLaw q false| =
        derivedBinfoldLimitLaw q true - derivedBinfoldLimitLaw q false := by
    change
      |Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q -
          Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q| =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q -
          Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q
    rw [abs_of_nonpos (sub_nonpos.mpr hcore)]
    ring
  have habs₂ :
      |derivedBinfoldLimitLaw q true - derivedBinfoldSwappedLaw q true| =
        derivedBinfoldLimitLaw q true - derivedBinfoldLimitLaw q false := by
    change
      |Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q -
          Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q| =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q -
          Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q
    rw [abs_of_nonneg (sub_nonneg.mpr hcore)]
  unfold derivedBinfoldTv xiEscortTvDistance
  rw [habs₁, habs₂]
  ring

private theorem derivedBinfoldBayes_closed (q : ℕ) :
    derivedBinfoldBayesError q = 1 / (1 + Real.goldenRatio ^ (q + 1)) := by
  have hsum : derivedBinfoldLimitLaw q false + derivedBinfoldLimitLaw q true = 1 := by
    simpa [derivedBinfoldLimitLaw] using
      Omega.Conclusion.binfoldTwoPointMasses_sum Real.goldenRatio q
  rw [derivedBinfoldBayesError, derivedBinfoldTv_closed]
  have hrewrite : derivedBinfoldLimitLaw q false = 1 / (1 + Real.goldenRatio ^ (q + 1)) :=
    derivedBinfoldMassLow_closed q
  nlinarith

/-- Paper label: `cor:derived-binfold-tv-bayes-constants`. The verified two-atom limit law gives
the exact limiting masses, the two-point TV is half of the `ℓ¹` distance, Bayes error equals
`(1 - D_TV) / 2`, and the exponential error term remains the audited escort-collapse rate. -/
theorem paper_derived_binfold_tv_bayes_constants : DerivedBinfoldTvBayesConstantsStatement := by
  refine ⟨?_, ?_⟩
  · intro q
    refine ⟨derivedBinfoldMassLow_closed q, derivedBinfoldMassHigh_closed q, rfl, rfl, ?_⟩
    exact derivedBinfoldBayes_closed q
  · intro m
    rfl

end

end Omega.Zeta
