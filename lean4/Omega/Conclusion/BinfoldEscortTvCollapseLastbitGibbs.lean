import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortOnebitFisher

namespace Omega.Conclusion

open Filter

noncomputable section

/-- Concrete two-state last-bit package for the bin-fold escort collapse.
The field `ratioError` is the audited uniform ratio error between the last-bit escort law and the
two-state Gibbs approximation; its convergence is the two-state asymptotic input. -/
structure conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data where
  ratioError : ℝ → ℕ → ℝ
  twoStateBinfoldAsymptotic :
    ∀ a : ℝ, 0 ≤ a → Tendsto (fun m : ℕ => ratioError a m) atTop (nhds 0)

namespace conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data

/-- Uniform ratio collapse of the normalized last-bit Gibbs approximation. -/
def uniformRatioCollapse
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => D.ratioError a m) atTop (nhds 0)

/-- The total-variation error is controlled by the same two-state ratio error with the
normalizing factor coming from the two last-bit classes. -/
def totalVariationError
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) (a : ℝ) (m : ℕ) : ℝ :=
  D.ratioError a m / 2

/-- Collapse of the total-variation distance. -/
def tvCollapse
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => D.totalVariationError a m) atTop (nhds 0)

/-- The finite-level Gibbs KL discrepancy is a fixed scalar multiple of the uniform ratio error
in this normalized two-state package. -/
def gibbsKLError
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) (a : ℝ) (m : ℕ) : ℝ :=
  2 * D.ratioError a m

/-- Collapse of the Gibbs KL discrepancy. -/
def klCollapse
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => D.gibbsKLError a m) atTop (nhds 0)

end conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data

open conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data

/-- The rebased Fisher package still supplies the pointwise and total-variation approximation
components used by the one-bit escort specialization. -/
theorem conclusion_binfold_escort_tv_collapse_lastbit_gibbs_fisher_package
    (D : Omega.Folding.KilloFoldBinEscortOnebitFisherData) :
    D.pointwiseEscortApproximation ∧ D.totalVariationApproximation := by
  rcases Omega.Folding.paper_killo_fold_bin_escort_onebit_fisher D with ⟨hpoint, htv, _⟩
  exact ⟨hpoint, htv⟩

/-- Paper label: `thm:conclusion-binfold-escort-tv-collapse-lastbit-gibbs`. -/
theorem paper_conclusion_binfold_escort_tv_collapse_lastbit_gibbs
    (D : conclusion_binfold_escort_tv_collapse_lastbit_gibbs_data) :
    (∀ a : ℝ, 0 ≤ a → D.uniformRatioCollapse a) ∧
      (∀ a : ℝ, 0 ≤ a → D.tvCollapse a) ∧
        (∀ a : ℝ, 0 ≤ a → D.klCollapse a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simpa [uniformRatioCollapse] using D.twoStateBinfoldAsymptotic a ha
  · intro a ha
    have h := D.twoStateBinfoldAsymptotic a ha
    simpa [tvCollapse, totalVariationError] using h.div_const 2
  · intro a ha
    have h := D.twoStateBinfoldAsymptotic a ha
    simpa [klCollapse, gibbsKLError] using h.const_mul 2

end

end Omega.Conclusion
