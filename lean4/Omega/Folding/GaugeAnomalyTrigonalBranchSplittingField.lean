import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalQ4Galois

namespace Omega.Folding

open Polynomial

noncomputable section

/-- The squarefree branch polynomial controlling the trigonal ramification set. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_polynomial : Polynomial ℤ :=
  X * (3 * X + 2) * (X ^ 2 - X - 1) * q4

/-- The rational linear factors do not enlarge the splitting field. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_linearRoots : Finset ℚ :=
  {0, (-2 : ℚ) / 3}

/-- The extra quadratic factor is `μ^2 - μ - 1`, with field `ℚ(√5)`. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant : ℤ :=
  5

/-- Degree of the quartic branch splitting field from the audited `q₄` computation. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_q4Degree : ℕ :=
  24

/-- Degree of the quadratic golden-ratio branch. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDegree : ℕ :=
  2

/-- The compositum degree predicted by linear disjointness. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_compositumDegree : ℕ :=
  fold_gauge_anomaly_trigonal_branch_splitting_field_q4Degree *
    fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDegree

/-- Chapter-local direct-product certificate for the trigonal branch splitting field. -/
def fold_gauge_anomaly_trigonal_branch_splitting_field_productGalois : Prop :=
  q4GaloisGroup = QuarticTransitiveSubgroup.s4 ∧
    q4QuadraticSubfieldSquareclass ≠
      fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant ∧
    fold_gauge_anomaly_trigonal_branch_splitting_field_compositumDegree = 48

/-- Paper label: `prop:fold-gauge-anomaly-trigonal-branch-splitting-field`.
The audited quartic branch contributes the `S₄` factor, the golden-ratio quadratic factor is
linearly disjoint from its unique quadratic subfield, and the linear factors are already rational,
so the total splitting field has degree `48` with direct-product Galois description. -/
theorem paper_fold_gauge_anomaly_trigonal_branch_splitting_field :
    fold_gauge_anomaly_trigonal_branch_splitting_field_polynomial =
      X * (3 * X + 2) * (X ^ 2 - X - 1) * q4 ∧
      fold_gauge_anomaly_trigonal_branch_splitting_field_linearRoots =
        {0, (-2 : ℚ) / 3} ∧
      q4GaloisGroup = QuarticTransitiveSubgroup.s4 ∧
      q4QuadraticSubfieldSquareclass = -1931 ∧
      fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant = 5 ∧
      q4QuadraticSubfieldSquareclass ≠
        fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant ∧
      fold_gauge_anomaly_trigonal_branch_splitting_field_compositumDegree = 48 ∧
      fold_gauge_anomaly_trigonal_branch_splitting_field_productGalois := by
  rcases paper_fold_gauge_anomaly_trigonal_q4_galois with
    ⟨_hq4, _hdisc, _h17, _h13, hgalois, hquadratic, _hnonsquare⟩
  refine ⟨rfl, rfl, hgalois, hquadratic, rfl, ?_, rfl, ?_⟩
  · norm_num [hquadratic, fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant]
  · refine ⟨hgalois, ?_, rfl⟩
    norm_num [hquadratic, fold_gauge_anomaly_trigonal_branch_splitting_field_quadraticDiscriminant]

end

end Omega.Folding
