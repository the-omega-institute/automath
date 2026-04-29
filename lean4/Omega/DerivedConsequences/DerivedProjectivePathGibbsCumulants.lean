import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open Finset
open scoped BigOperators

/-- Finite path ensemble used to package the Gibbs cumulant identities. -/
structure DerivedProjectivePathGibbsCumulantsData where
  Path : Type
  instFintypePath : Fintype Path
  instDecidableEqPath : DecidableEq Path
  path_nonempty : Nonempty Path
  energy : Path → ℝ
  beta : ℝ

attribute [instance] DerivedProjectivePathGibbsCumulantsData.instFintypePath
attribute [instance] DerivedProjectivePathGibbsCumulantsData.instDecidableEqPath

namespace DerivedProjectivePathGibbsCumulantsData

/-- Unnormalized Boltzmann weight of a finite path. -/
noncomputable def derived_projective_path_gibbs_cumulants_pathWeight
    (D : DerivedProjectivePathGibbsCumulantsData) (x : D.Path) : ℝ :=
  Real.exp (-D.beta * D.energy x)

/-- Finite partition function. -/
noncomputable def derived_projective_path_gibbs_cumulants_partition
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  ∑ x, D.derived_projective_path_gibbs_cumulants_pathWeight x

/-- Score variable appearing in the logarithmic derivative. -/
def derived_projective_path_gibbs_cumulants_score (D : DerivedProjectivePathGibbsCumulantsData)
    (x : D.Path) : ℝ :=
  -D.energy x

/-- Termwise derivative of the finite partition sum. -/
noncomputable def derived_projective_path_gibbs_cumulants_partitionDeriv
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  ∑ x, D.derived_projective_path_gibbs_cumulants_score x *
    D.derived_projective_path_gibbs_cumulants_pathWeight x

/-- Termwise second derivative of the finite partition sum. -/
noncomputable def derived_projective_path_gibbs_cumulants_partitionSecondDeriv
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  ∑ x, (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 *
    D.derived_projective_path_gibbs_cumulants_pathWeight x

/-- Gibbs normalization of a path weight. -/
noncomputable def derived_projective_path_gibbs_cumulants_gibbsWeight
    (D : DerivedProjectivePathGibbsCumulantsData) (x : D.Path) : ℝ :=
  D.derived_projective_path_gibbs_cumulants_pathWeight x /
    D.derived_projective_path_gibbs_cumulants_partition

/-- Weighted average under the normalized Gibbs law. -/
noncomputable def derived_projective_path_gibbs_cumulants_gibbsAverage
    (D : DerivedProjectivePathGibbsCumulantsData) (f : D.Path → ℝ) : ℝ :=
  ∑ x, D.derived_projective_path_gibbs_cumulants_gibbsWeight x * f x

/-- Logarithmic derivative written as quotient `Z' / Z`. -/
noncomputable def derived_projective_path_gibbs_cumulants_logPartitionFirstDerivative
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  D.derived_projective_path_gibbs_cumulants_partitionDeriv /
    D.derived_projective_path_gibbs_cumulants_partition

/-- Quotient-rule expression for the second logarithmic derivative. -/
noncomputable def derived_projective_path_gibbs_cumulants_logPartitionSecondDerivative
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  D.derived_projective_path_gibbs_cumulants_partitionSecondDeriv /
      D.derived_projective_path_gibbs_cumulants_partition -
    (D.derived_projective_path_gibbs_cumulants_partitionDeriv /
      D.derived_projective_path_gibbs_cumulants_partition) ^ 2

/-- Variance of the score under the Gibbs law. -/
noncomputable def derived_projective_path_gibbs_cumulants_gibbsVariance
    (D : DerivedProjectivePathGibbsCumulantsData) : ℝ :=
  D.derived_projective_path_gibbs_cumulants_gibbsAverage
      (fun x => (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) -
    (D.derived_projective_path_gibbs_cumulants_gibbsAverage
      D.derived_projective_path_gibbs_cumulants_score) ^ 2

/-- First cumulant identity: the log-derivative is the Gibbs average of the score. -/
def firstDerivativeFormula (D : DerivedProjectivePathGibbsCumulantsData) : Prop :=
  D.derived_projective_path_gibbs_cumulants_logPartitionFirstDerivative =
    D.derived_projective_path_gibbs_cumulants_gibbsAverage
      D.derived_projective_path_gibbs_cumulants_score

/-- Second cumulant identity: the second log-derivative is the Gibbs variance of the score. -/
def secondDerivativeFormula (D : DerivedProjectivePathGibbsCumulantsData) : Prop :=
  D.derived_projective_path_gibbs_cumulants_logPartitionSecondDerivative =
    D.derived_projective_path_gibbs_cumulants_gibbsVariance

lemma derived_projective_path_gibbs_cumulants_partition_pos
    (D : DerivedProjectivePathGibbsCumulantsData) :
    0 < D.derived_projective_path_gibbs_cumulants_partition := by
  classical
  rcases D.path_nonempty with ⟨x₀⟩
  have hx₀_mem : x₀ ∈ (Finset.univ : Finset D.Path) := by
    simp
  have hx₀ :
      D.derived_projective_path_gibbs_cumulants_pathWeight x₀ ≤
        D.derived_projective_path_gibbs_cumulants_partition := by
    unfold derived_projective_path_gibbs_cumulants_partition
    simpa [derived_projective_path_gibbs_cumulants_pathWeight] using
      (Finset.single_le_sum
        (f := fun y : D.Path => Real.exp (-D.beta * D.energy y))
        (fun y _ => le_of_lt (Real.exp_pos _))
        hx₀_mem)
  exact lt_of_lt_of_le (Real.exp_pos _) hx₀

lemma derived_projective_path_gibbs_cumulants_gibbsWeight_sum
    (D : DerivedProjectivePathGibbsCumulantsData) :
    (∑ x, D.derived_projective_path_gibbs_cumulants_gibbsWeight x) = 1 := by
  calc
    (∑ x, D.derived_projective_path_gibbs_cumulants_gibbsWeight x)
        = (∑ x, D.derived_projective_path_gibbs_cumulants_pathWeight x) /
            D.derived_projective_path_gibbs_cumulants_partition := by
              unfold derived_projective_path_gibbs_cumulants_gibbsWeight
              rw [Finset.sum_div]
    _ = 1 := by
          simpa [derived_projective_path_gibbs_cumulants_partition] using
            div_self D.derived_projective_path_gibbs_cumulants_partition_pos.ne'

lemma derived_projective_path_gibbs_cumulants_first_moment
    (D : DerivedProjectivePathGibbsCumulantsData) :
    D.derived_projective_path_gibbs_cumulants_logPartitionFirstDerivative =
      D.derived_projective_path_gibbs_cumulants_gibbsAverage
        D.derived_projective_path_gibbs_cumulants_score := by
  calc
    D.derived_projective_path_gibbs_cumulants_logPartitionFirstDerivative
        = (∑ x, D.derived_projective_path_gibbs_cumulants_score x *
            D.derived_projective_path_gibbs_cumulants_pathWeight x) /
            D.derived_projective_path_gibbs_cumulants_partition := by
              rfl
    _ = ∑ x,
          (D.derived_projective_path_gibbs_cumulants_score x *
            D.derived_projective_path_gibbs_cumulants_pathWeight x) /
            D.derived_projective_path_gibbs_cumulants_partition := by
              rw [Finset.sum_div]
    _ = ∑ x,
          D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
            D.derived_projective_path_gibbs_cumulants_score x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [derived_projective_path_gibbs_cumulants_gibbsWeight, div_eq_mul_inv,
                mul_comm, mul_assoc]
    _ = D.derived_projective_path_gibbs_cumulants_gibbsAverage
          D.derived_projective_path_gibbs_cumulants_score := by
            rfl

lemma derived_projective_path_gibbs_cumulants_second_moment
    (D : DerivedProjectivePathGibbsCumulantsData) :
    D.derived_projective_path_gibbs_cumulants_partitionSecondDeriv /
        D.derived_projective_path_gibbs_cumulants_partition =
      D.derived_projective_path_gibbs_cumulants_gibbsAverage
        (fun x => (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) := by
  calc
    D.derived_projective_path_gibbs_cumulants_partitionSecondDeriv /
        D.derived_projective_path_gibbs_cumulants_partition
        = (∑ x, (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 *
            D.derived_projective_path_gibbs_cumulants_pathWeight x) /
            D.derived_projective_path_gibbs_cumulants_partition := by
              rfl
    _ = ∑ x,
          ((D.derived_projective_path_gibbs_cumulants_score x) ^ 2 *
            D.derived_projective_path_gibbs_cumulants_pathWeight x) /
            D.derived_projective_path_gibbs_cumulants_partition := by
              rw [Finset.sum_div]
    _ = ∑ x,
          D.derived_projective_path_gibbs_cumulants_gibbsWeight x *
            (D.derived_projective_path_gibbs_cumulants_score x) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [derived_projective_path_gibbs_cumulants_gibbsWeight, div_eq_mul_inv,
                mul_comm, mul_assoc]
    _ = D.derived_projective_path_gibbs_cumulants_gibbsAverage
          (fun x => (D.derived_projective_path_gibbs_cumulants_score x) ^ 2) := by
            rfl

end DerivedProjectivePathGibbsCumulantsData

open DerivedProjectivePathGibbsCumulantsData

/-- Paper label: `thm:derived-projective-path-gibbs-cumulants`. For a finite path ensemble, the
first logarithmic derivative of the partition function is the Gibbs average of the score and the
second logarithmic derivative is the corresponding Gibbs variance. -/
theorem paper_derived_projective_path_gibbs_cumulants
    (D : DerivedProjectivePathGibbsCumulantsData) :
    D.firstDerivativeFormula ∧ D.secondDerivativeFormula := by
  refine ⟨D.derived_projective_path_gibbs_cumulants_first_moment, ?_⟩
  have hfirst :
      D.derived_projective_path_gibbs_cumulants_partitionDeriv /
          D.derived_projective_path_gibbs_cumulants_partition =
        D.derived_projective_path_gibbs_cumulants_gibbsAverage
          D.derived_projective_path_gibbs_cumulants_score := by
    simpa [derived_projective_path_gibbs_cumulants_logPartitionFirstDerivative] using
      D.derived_projective_path_gibbs_cumulants_first_moment
  unfold secondDerivativeFormula
  unfold derived_projective_path_gibbs_cumulants_logPartitionSecondDerivative
  unfold derived_projective_path_gibbs_cumulants_gibbsVariance
  rw [DerivedProjectivePathGibbsCumulantsData.derived_projective_path_gibbs_cumulants_second_moment,
    hfirst]

end Omega.DerivedConsequences
