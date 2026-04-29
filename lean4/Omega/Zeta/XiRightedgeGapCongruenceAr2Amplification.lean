import Omega.Zeta.XiAbelRightedgeGapAr2ExpError
import Mathlib.Tactic

namespace Omega.Zeta

/-- The `j`-th congruence subsequence of an observable. -/
def xi_rightedge_gap_congruence_ar2_amplification_subsequence
    (E : ℕ → ℂ) (m j : ℕ) : ℕ → ℂ :=
  fun n => E (m * n + j)

/-- The residual restricted to the same congruence channel. -/
def xi_rightedge_gap_congruence_ar2_amplification_residualSubsequence
    (r : ℕ → ℂ) (m j : ℕ) : ℕ → ℂ :=
  fun n => r (m * n + j)

/-- AR(2) data obtained from the base right-edge expansion by passing to one congruence channel. -/
def xi_rightedge_gap_congruence_ar2_amplification_data
    (E r : ℕ → ℂ) (alpha amplitude : ℂ) (m j : ℕ) :
    xi_abel_rightedge_gap_ar2_exp_error_data where
  alpha := alpha ^ m
  amplitude := amplitude * alpha ^ j
  observable := xi_rightedge_gap_congruence_ar2_amplification_subsequence E m j
  residual := xi_rightedge_gap_congruence_ar2_amplification_residualSubsequence r m j

/-- Paper label: `cor:xi-rightedge-gap-congruence-ar2-amplification`.
Specializing the base right-edge expansion to `n ↦ m*n+j` gives the same exact AR(2)
cancellation for every congruence channel, with characteristic root `alpha^m`. -/
theorem paper_xi_rightedge_gap_congruence_ar2_amplification
    (E : ℕ → ℂ) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (alpha amplitude : ℂ) (residual : ℕ → ℂ),
      (∀ n : ℕ,
        E n =
          amplitude * alpha ^ n + star amplitude * (star alpha) ^ n + residual n) →
        ∀ j : ℕ,
          let D :=
            xi_rightedge_gap_congruence_ar2_amplification_data E residual alpha amplitude m j
          D.ar2_exp_error_bound ∧ D.coefficient_identities := by
  have _hm_steps : 2 ≤ m := hm
  intro alpha amplitude residual hbase j
  let D := xi_rightedge_gap_congruence_ar2_amplification_data E residual alpha amplitude m j
  have hgap : D.right_edge_gap_hypotheses := by
    intro n
    dsimp [D, xi_rightedge_gap_congruence_ar2_amplification_data,
      xi_rightedge_gap_congruence_ar2_amplification_subsequence,
      xi_rightedge_gap_congruence_ar2_amplification_residualSubsequence]
    rw [hbase (m * n + j)]
    simp only [map_mul, map_pow]
    rw [pow_add, pow_mul]
    rw [pow_add, pow_mul]
    ring_nf
    ac_rfl
  exact paper_xi_abel_rightedge_gap_ar2_exp_error D hgap

end Omega.Zeta
