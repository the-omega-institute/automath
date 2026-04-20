import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Folding

/-- The two-state Gibbs proxy induced by the escort logistic parameter on the last-bit partition.
-/
noncomputable def killoOnebitGibbsProxy (q : ℝ) (b : Bool) : ℝ :=
  if b then killoEscortTheta q else 1 - killoEscortTheta q

lemma killoOnebitGibbsProxy_sum (q : ℝ) :
    killoOnebitGibbsProxy q false + killoOnebitGibbsProxy q true = 1 := by
  simp [killoOnebitGibbsProxy]

/-- Concrete data for the one-bit escort/Gibbs comparison. The escort law is a probability measure
on the last-bit partition, and the pointwise relative error is measured against the two-state Gibbs
proxy coming from the escort logistic parameter. -/
structure KilloFoldBinEscortOnebitFisherData where
  q : ℝ
  escortLaw : Bool → ℝ
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  escortLaw_nonneg : ∀ b, 0 ≤ escortLaw b
  escortLaw_total : escortLaw false + escortLaw true = 1
  uniform_relative_error :
    ∀ b,
      |escortLaw b - killoOnebitGibbsProxy q b| ≤ relativeError * killoOnebitGibbsProxy q b

namespace KilloFoldBinEscortOnebitFisherData

/-- Uniform pointwise multiplicative comparison between the escort law and the Gibbs proxy. -/
def pointwiseEscortApproximation (D : KilloFoldBinEscortOnebitFisherData) : Prop :=
  ∀ b,
    |D.escortLaw b - killoOnebitGibbsProxy D.q b| ≤ D.relativeError * killoOnebitGibbsProxy D.q b

/-- Total variation distance on the two-point last-bit partition. -/
noncomputable def totalVariationDistance (D : KilloFoldBinEscortOnebitFisherData) : ℝ :=
  (|D.escortLaw false - killoOnebitGibbsProxy D.q false| +
      |D.escortLaw true - killoOnebitGibbsProxy D.q true|) /
    2

/-- Summing the pointwise relative errors gives a total-variation estimate. -/
def totalVariationApproximation (D : KilloFoldBinEscortOnebitFisherData) : Prop :=
  D.totalVariationDistance ≤ D.relativeError / 2

/-- Normalized law on the two last-bit fibers `A₀,A₁`. -/
noncomputable def normalizedLastBitLaw (μ : Bool → ℝ) (b : Bool) : ℝ :=
  μ b / (μ false + μ true)

/-- After normalizing on the last-bit fibers, the escort law still obeys the same uniform
comparison with the two-state Gibbs proxy. -/
def lastBitAsymptoticallySufficient (D : KilloFoldBinEscortOnebitFisherData) : Prop :=
  ∀ b,
    |normalizedLastBitLaw D.escortLaw b - killoOnebitGibbsProxy D.q b| ≤
      D.relativeError * killoOnebitGibbsProxy D.q b

end KilloFoldBinEscortOnebitFisherData

open KilloFoldBinEscortOnebitFisherData

/-- Packaging the uniform last-bit escort/Gibbs comparison yields the pointwise bound, its
two-state total-variation consequence, and the normalized last-bit sufficiency statement.
    thm:killo-fold-bin-escort-onebit-fisher -/
theorem paper_killo_fold_bin_escort_onebit_fisher (D : KilloFoldBinEscortOnebitFisherData) :
    D.pointwiseEscortApproximation ∧
      D.totalVariationApproximation ∧
      D.lastBitAsymptoticallySufficient := by
  refine ⟨D.uniform_relative_error, ?_, ?_⟩
  · have hsum :
      |D.escortLaw false - killoOnebitGibbsProxy D.q false| +
          |D.escortLaw true - killoOnebitGibbsProxy D.q true| ≤
        D.relativeError * killoOnebitGibbsProxy D.q false +
          D.relativeError * killoOnebitGibbsProxy D.q true := by
      exact add_le_add (D.uniform_relative_error false) (D.uniform_relative_error true)
    calc
      D.totalVariationDistance =
          (|D.escortLaw false - killoOnebitGibbsProxy D.q false| +
              |D.escortLaw true - killoOnebitGibbsProxy D.q true|) /
            2 := by
            rfl
      _ ≤
          (D.relativeError * killoOnebitGibbsProxy D.q false +
              D.relativeError * killoOnebitGibbsProxy D.q true) /
            2 := by
            exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
      _ = D.relativeError / 2 := by
            rw [show D.relativeError * killoOnebitGibbsProxy D.q false +
                D.relativeError * killoOnebitGibbsProxy D.q true =
                  D.relativeError *
                    (killoOnebitGibbsProxy D.q false + killoOnebitGibbsProxy D.q true) by ring]
            rw [killoOnebitGibbsProxy_sum]
            ring
  · intro b
    have hnormalize : normalizedLastBitLaw D.escortLaw b = D.escortLaw b := by
      simp [normalizedLastBitLaw, D.escortLaw_total]
    rw [hnormalize]
    exact D.uniform_relative_error b

end Omega.Folding
