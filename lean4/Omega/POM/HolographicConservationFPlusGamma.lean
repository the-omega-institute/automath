import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The seed first moment in the holographic conservation normalization. -/
def pom_holographic_conservation_f_plus_gamma_S_one (m : ℕ) : ℕ :=
  2 ^ m

/-- The seed pressure at the Shannon point. -/
def pom_holographic_conservation_f_plus_gamma_tau (_q : ℝ) : ℝ :=
  Real.log (2 : ℝ)

/-- The affine layer spectrum saturating the conservation line. -/
def pom_holographic_conservation_f_plus_gamma_f (gamma : ℝ) : ℝ :=
  Real.log (2 : ℝ) - gamma

/-- Paper-facing statement for `cor:pom-holographic-conservation-f-plus-gamma`. The concrete seed
records `S₁(m)=2^m`, `tau(1)=log 2`, the `q=1` supremum identity, and the resulting pointwise
conservation bound. -/
def pom_holographic_conservation_f_plus_gamma_statement : Prop :=
  (∀ m : ℕ, pom_holographic_conservation_f_plus_gamma_S_one m = 2 ^ m) ∧
    pom_holographic_conservation_f_plus_gamma_tau 1 = Real.log (2 : ℝ) ∧
    sSup
        ((fun gamma : ℝ =>
            pom_holographic_conservation_f_plus_gamma_f gamma + gamma) ''
          Set.Icc 0 (Real.log (2 : ℝ))) =
      Real.log (2 : ℝ) ∧
    ∀ gamma : ℝ,
      pom_holographic_conservation_f_plus_gamma_f gamma ≤ Real.log (2 : ℝ) - gamma

theorem paper_pom_holographic_conservation_f_plus_gamma :
    pom_holographic_conservation_f_plus_gamma_statement := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro m
    rfl
  · have hlog_nonneg : 0 ≤ Real.log (2 : ℝ) := by
      exact Real.log_nonneg (by norm_num)
    have hGreatest :
        IsGreatest
          ((fun gamma : ℝ =>
              pom_holographic_conservation_f_plus_gamma_f gamma + gamma) ''
            Set.Icc 0 (Real.log (2 : ℝ)))
          (Real.log (2 : ℝ)) := by
      refine ⟨?_, ?_⟩
      · refine ⟨0, ⟨le_rfl, hlog_nonneg⟩, ?_⟩
        simp [pom_holographic_conservation_f_plus_gamma_f]
      · intro y hy
        rcases hy with ⟨gamma, _hgamma, rfl⟩
        simp [pom_holographic_conservation_f_plus_gamma_f]
    exact hGreatest.csSup_eq
  · intro gamma
    rfl

end

end Omega.POM
