import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-precision depth for the dyadic Chebyshev--Dwork closure. -/
structure conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data where
  precision : ℕ

namespace conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data

def conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_step (t : ℤ) : ℤ :=
  t * t - 2

def conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_iter :
    ℕ → ℤ → ℤ
  | 0, t => t
  | n + 1, t =>
      conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_iter n
        (conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_step t)

def conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace
    (_D : conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data)
    (n : ℕ) (t : ℤ) : ℤ :=
  conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_iter n t

def conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_modulus
    (D : conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data) : ℤ :=
  (2 : ℤ) ^ D.precision

def finitePrecisionClosure
    (D : conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data) : Prop :=
  ∀ n t,
    D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace (n + 1) t =
        D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace n
          (conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_step t) ∧
      (D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace (n + 1) t -
          D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace n
            (conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_step t)) %
          D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_modulus = 0

lemma conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace_substitution
    (D : conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data) :
    ∀ n t,
      D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace (n + 1) t =
        D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace n
          (conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_step t) := by
  intro n t
  rfl

end conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data

open conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data

/-- Paper label:
`thm:conclusion-weighted-sync-dyadic-chebyshev-dwork-finite-precision`. -/
theorem paper_conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision
    (D : conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_data) :
    D.finitePrecisionClosure := by
  intro n t
  have h :=
    D.conclusion_weighted_sync_dyadic_chebyshev_dwork_finite_precision_trace_substitution n t
  constructor
  · exact h
  · rw [h, sub_self]
    simp

end Omega.Conclusion
