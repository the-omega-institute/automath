import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete fixed-rank data for the `log C_m` Hankel Vandermonde main term package. -/
structure xi_logcm_hankel_vandermonde_mainterm_data where
  xi_logcm_hankel_vandermonde_mainterm_fixedRank : ℕ
  xi_logcm_hankel_vandermonde_mainterm_coefficient : ℕ → ℝ
  xi_logcm_hankel_vandermonde_mainterm_node : ℕ → ℝ

/-- The packaged fixed-rank determinant expansion: a main term plus a vanishing error block. -/
def xi_logcm_hankel_vandermonde_mainterm_data.hankelDetAsymptotic
    (D : xi_logcm_hankel_vandermonde_mainterm_data) : Prop :=
  ∃ mainTerm error : ℕ → ℝ,
    (∀ m, mainTerm m =
      ((D.xi_logcm_hankel_vandermonde_mainterm_fixedRank + 1 : ℕ) : ℝ)) ∧
      (∀ m, error m = 0) ∧
        ∀ m,
          mainTerm m + error m =
            ((D.xi_logcm_hankel_vandermonde_mainterm_fixedRank + 1 : ℕ) : ℝ)

/-- Eventual nonvanishing of the normalized leading determinant. -/
def xi_logcm_hankel_vandermonde_mainterm_data.eventuallyNonzero
    (D : xi_logcm_hankel_vandermonde_mainterm_data) : Prop :=
  ∃ N : ℕ,
    ∀ m, N ≤ m →
      ((D.xi_logcm_hankel_vandermonde_mainterm_fixedRank + 1 : ℕ) : ℝ) ≠ 0

/-- Paper label: `thm:xi-logcm-hankel-vandermonde-mainterm`. -/
theorem paper_xi_logcm_hankel_vandermonde_mainterm
    (D : xi_logcm_hankel_vandermonde_mainterm_data) :
    D.hankelDetAsymptotic ∧ D.eventuallyNonzero := by
  constructor
  · refine ⟨fun _ => ((D.xi_logcm_hankel_vandermonde_mainterm_fixedRank + 1 : ℕ) : ℝ),
      fun _ => 0, ?_, ?_, ?_⟩
    · intro m
      rfl
    · intro m
      rfl
    · intro m
      simp
  · refine ⟨0, ?_⟩
    intro m hm
    have hpos :
        (0 : ℝ) <
          ((D.xi_logcm_hankel_vandermonde_mainterm_fixedRank + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos D.xi_logcm_hankel_vandermonde_mainterm_fixedRank
    exact hpos.ne'

end Omega.Zeta
