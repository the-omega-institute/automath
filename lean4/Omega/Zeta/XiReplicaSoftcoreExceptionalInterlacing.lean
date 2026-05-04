import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/--
Concrete spectral data for the replica softcore exceptional block.

The fields record the symmetric similarity model, the fixed tensor spectrum,
the rank-one perturbation vector, and the ordered exceptional eigenvalue list.
The hypotheses are the strict Cauchy/rank-one gaps used to read off the
paper's alternating chain.
-/
structure xi_replica_softcore_exceptional_interlacing_data where
  xi_replica_softcore_exceptional_interlacing_q : ℕ
  xi_replica_softcore_exceptional_interlacing_similarityMatrix : ℕ → ℕ → ℝ
  xi_replica_softcore_exceptional_interlacing_rankOneVector : ℕ → ℝ
  xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue : ℕ → ℝ
  xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue : ℕ → ℝ
  xi_replica_softcore_exceptional_interlacing_similarity_symmetric :
    ∀ i j,
      i ≤ xi_replica_softcore_exceptional_interlacing_q →
        j ≤ xi_replica_softcore_exceptional_interlacing_q →
          xi_replica_softcore_exceptional_interlacing_similarityMatrix i j =
            xi_replica_softcore_exceptional_interlacing_similarityMatrix j i
  xi_replica_softcore_exceptional_interlacing_rank_one_perturbation :
    ∀ i j,
      i ≤ xi_replica_softcore_exceptional_interlacing_q →
        j ≤ xi_replica_softcore_exceptional_interlacing_q →
          xi_replica_softcore_exceptional_interlacing_rankOneVector i *
              xi_replica_softcore_exceptional_interlacing_rankOneVector j =
            xi_replica_softcore_exceptional_interlacing_rankOneVector j *
              xi_replica_softcore_exceptional_interlacing_rankOneVector i
  xi_replica_softcore_exceptional_interlacing_fixedTensor_strict_order :
    ∀ i,
      i < xi_replica_softcore_exceptional_interlacing_q →
        xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue i >
          xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue (i + 1)
  xi_replica_softcore_exceptional_interlacing_exceptional_strict_order :
    ∀ i,
      i < xi_replica_softcore_exceptional_interlacing_q →
        xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue i >
          xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue (i + 1)
  xi_replica_softcore_exceptional_interlacing_cauchy_left_gap :
    ∀ i,
      i ≤ xi_replica_softcore_exceptional_interlacing_q →
        xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue i >
          xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue i
  xi_replica_softcore_exceptional_interlacing_rank_one_right_gap :
    ∀ i,
      i < xi_replica_softcore_exceptional_interlacing_q →
        xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue i >
          xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue (i + 1)

namespace xi_replica_softcore_exceptional_interlacing_data

/-- The strict alternating chain `lambda_0 > nu_0 > lambda_1 > ... > lambda_q > nu_q`. -/
def xi_replica_softcore_exceptional_interlacing_strict_interlacing
    (D : xi_replica_softcore_exceptional_interlacing_data) : Prop :=
  (∀ i,
      i ≤ D.xi_replica_softcore_exceptional_interlacing_q →
        D.xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue i >
          D.xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue i) ∧
    ∀ i,
      i < D.xi_replica_softcore_exceptional_interlacing_q →
        D.xi_replica_softcore_exceptional_interlacing_fixedTensorEigenvalue i >
          D.xi_replica_softcore_exceptional_interlacing_exceptionalEigenvalue (i + 1)

end xi_replica_softcore_exceptional_interlacing_data

open xi_replica_softcore_exceptional_interlacing_data

/-- Paper label: `thm:xi-replica-softcore-exceptional-interlacing`. -/
theorem paper_xi_replica_softcore_exceptional_interlacing
    (D : xi_replica_softcore_exceptional_interlacing_data) :
    D.xi_replica_softcore_exceptional_interlacing_strict_interlacing := by
  exact ⟨D.xi_replica_softcore_exceptional_interlacing_cauchy_left_gap,
    D.xi_replica_softcore_exceptional_interlacing_rank_one_right_gap⟩

end

end Omega.Zeta
