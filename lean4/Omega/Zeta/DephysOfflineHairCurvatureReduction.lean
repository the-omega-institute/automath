import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete bounded-slice interface data for offline hair curvature reduction. -/
structure dephys_offline_hair_curvature_reduction_Data where
  dephys_offline_hair_curvature_reduction_Slice : Type u
  dephys_offline_hair_curvature_reduction_normalForm :
    dephys_offline_hair_curvature_reduction_Slice →
      dephys_offline_hair_curvature_reduction_Slice
  dephys_offline_hair_curvature_reduction_quotient :
    dephys_offline_hair_curvature_reduction_Slice →
      dephys_offline_hair_curvature_reduction_Slice
  dephys_offline_hair_curvature_reduction_anomaly :
    dephys_offline_hair_curvature_reduction_Slice → ℤ
  dephys_offline_hair_curvature_reduction_moment :
    ℕ → dephys_offline_hair_curvature_reduction_Slice → ℤ
  dephys_offline_hair_curvature_reduction_amplification : ℤ
  dephys_offline_hair_curvature_reduction_frontier :
    List dephys_offline_hair_curvature_reduction_Slice
  dephys_offline_hair_curvature_reduction_epsilonNormal :
    dephys_offline_hair_curvature_reduction_Slice → ℝ
  dephys_offline_hair_curvature_reduction_epsilonStrict :
    dephys_offline_hair_curvature_reduction_Slice → ℝ
  dephys_offline_hair_curvature_reduction_errorComposite :
    dephys_offline_hair_curvature_reduction_Slice → ℝ
  dephys_offline_hair_curvature_reduction_normalForm_anomaly_invariant :
    ∀ x,
      dephys_offline_hair_curvature_reduction_anomaly
          (dephys_offline_hair_curvature_reduction_normalForm x) =
        dephys_offline_hair_curvature_reduction_anomaly x
  dephys_offline_hair_curvature_reduction_zero_anomaly_BC_strict :
    ∀ x,
      dephys_offline_hair_curvature_reduction_anomaly x = 0 →
        dephys_offline_hair_curvature_reduction_quotient
            (dephys_offline_hair_curvature_reduction_normalForm x) =
          dephys_offline_hair_curvature_reduction_quotient x
  dephys_offline_hair_curvature_reduction_universal_quotient_factorization :
    ∀ (f :
        dephys_offline_hair_curvature_reduction_Slice →
          dephys_offline_hair_curvature_reduction_Slice),
      (∀ x y,
        dephys_offline_hair_curvature_reduction_quotient x =
          dephys_offline_hair_curvature_reduction_quotient y →
            f x = f y) →
        ∃ g :
          dephys_offline_hair_curvature_reduction_Slice →
            dephys_offline_hair_curvature_reduction_Slice,
          ∀ x, g (dephys_offline_hair_curvature_reduction_quotient x) = f x
  dephys_offline_hair_curvature_reduction_moment_amplification :
    ∀ k x,
      dephys_offline_hair_curvature_reduction_moment (k + 1)
          (dephys_offline_hair_curvature_reduction_normalForm x) =
        dephys_offline_hair_curvature_reduction_moment k x +
          dephys_offline_hair_curvature_reduction_amplification *
            dephys_offline_hair_curvature_reduction_anomaly x
  dephys_offline_hair_curvature_reduction_finite_frontier_search :
    ∀ x,
      ∃ y ∈ dephys_offline_hair_curvature_reduction_frontier,
        dephys_offline_hair_curvature_reduction_quotient y =
          dephys_offline_hair_curvature_reduction_quotient
            (dephys_offline_hair_curvature_reduction_normalForm x)
  dephys_offline_hair_curvature_reduction_epsilon_budget_composition :
    ∀ x,
      dephys_offline_hair_curvature_reduction_errorComposite x ≤
        dephys_offline_hair_curvature_reduction_epsilonNormal x +
          dephys_offline_hair_curvature_reduction_epsilonStrict x

/-- Six concrete outputs of the offline-hair curvature reduction interface. -/
def dephys_offline_hair_curvature_reduction_statement
    (D : dephys_offline_hair_curvature_reduction_Data) : Prop :=
  (∀ x,
      D.dephys_offline_hair_curvature_reduction_anomaly
          (D.dephys_offline_hair_curvature_reduction_normalForm x) =
        D.dephys_offline_hair_curvature_reduction_anomaly x) ∧
    (∀ x,
      D.dephys_offline_hair_curvature_reduction_anomaly x = 0 →
        D.dephys_offline_hair_curvature_reduction_quotient
            (D.dephys_offline_hair_curvature_reduction_normalForm x) =
          D.dephys_offline_hair_curvature_reduction_quotient x ∧
        D.dephys_offline_hair_curvature_reduction_anomaly
            (D.dephys_offline_hair_curvature_reduction_normalForm x) = 0) ∧
    (∀ (f :
        D.dephys_offline_hair_curvature_reduction_Slice →
          D.dephys_offline_hair_curvature_reduction_Slice),
      (∀ x y,
        D.dephys_offline_hair_curvature_reduction_quotient x =
          D.dephys_offline_hair_curvature_reduction_quotient y →
            f x = f y) →
        ∃ g :
          D.dephys_offline_hair_curvature_reduction_Slice →
            D.dephys_offline_hair_curvature_reduction_Slice,
          ∀ x, g (D.dephys_offline_hair_curvature_reduction_quotient x) = f x) ∧
    (∀ k x,
      D.dephys_offline_hair_curvature_reduction_moment (k + 1)
          (D.dephys_offline_hair_curvature_reduction_normalForm x) =
        D.dephys_offline_hair_curvature_reduction_moment k x +
          D.dephys_offline_hair_curvature_reduction_amplification *
            D.dephys_offline_hair_curvature_reduction_anomaly x) ∧
    (∀ x,
      ∃ y ∈ D.dephys_offline_hair_curvature_reduction_frontier,
        D.dephys_offline_hair_curvature_reduction_quotient y =
          D.dephys_offline_hair_curvature_reduction_quotient
            (D.dephys_offline_hair_curvature_reduction_normalForm x)) ∧
    (∀ x,
      D.dephys_offline_hair_curvature_reduction_errorComposite x ≤
        D.dephys_offline_hair_curvature_reduction_epsilonNormal x +
          D.dephys_offline_hair_curvature_reduction_epsilonStrict x)

/-- Paper label: `thm:dephys-offline-hair-curvature-reduction`. -/
theorem paper_dephys_offline_hair_curvature_reduction
    (D : dephys_offline_hair_curvature_reduction_Data) :
    dephys_offline_hair_curvature_reduction_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.dephys_offline_hair_curvature_reduction_normalForm_anomaly_invariant
  · intro x hx
    refine ⟨D.dephys_offline_hair_curvature_reduction_zero_anomaly_BC_strict x hx, ?_⟩
    rw [D.dephys_offline_hair_curvature_reduction_normalForm_anomaly_invariant x, hx]
  · exact D.dephys_offline_hair_curvature_reduction_universal_quotient_factorization
  · exact D.dephys_offline_hair_curvature_reduction_moment_amplification
  · exact D.dephys_offline_hair_curvature_reduction_finite_frontier_search
  · exact D.dephys_offline_hair_curvature_reduction_epsilon_budget_composition

end Omega.Zeta
