import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Jensen-defect certificate data for the horizon purity criterion. -/
structure xi_horizon_purity_criterion_data where
  xi_horizon_purity_criterion_zeroMultiplicity : ℕ → ℕ
  xi_horizon_purity_criterion_jensenDefect : ℕ → ℝ
  xi_horizon_purity_criterion_rh_implies_vanishing :
    (∀ n : ℕ, xi_horizon_purity_criterion_zeroMultiplicity n = 0) →
      ∀ n : ℕ, xi_horizon_purity_criterion_jensenDefect n = 0
  xi_horizon_purity_criterion_vanishing_implies_rh :
    (∀ n : ℕ, xi_horizon_purity_criterion_jensenDefect n = 0) →
      ∀ n : ℕ, xi_horizon_purity_criterion_zeroMultiplicity n = 0
  xi_horizon_purity_criterion_not_rh_has_disk_zero :
    (¬ ∀ n : ℕ, xi_horizon_purity_criterion_zeroMultiplicity n = 0) →
      ∃ n : ℕ, 0 < xi_horizon_purity_criterion_zeroMultiplicity n
  xi_horizon_purity_criterion_positive_liminf_from_disk_zero :
    ∀ n : ℕ, 0 < xi_horizon_purity_criterion_zeroMultiplicity n →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
          δ ≤ xi_horizon_purity_criterion_jensenDefect k

/-- The no-disk-zero predicate used as the formal RH proxy. -/
def xi_horizon_purity_criterion_rh
    (D : xi_horizon_purity_criterion_data) : Prop :=
  ∀ n : ℕ, D.xi_horizon_purity_criterion_zeroMultiplicity n = 0

/-- Vanishing of the Jensen defect sequence. -/
def xi_horizon_purity_criterion_vanishing_jensen_defect
    (D : xi_horizon_purity_criterion_data) : Prop :=
  ∀ n : ℕ, D.xi_horizon_purity_criterion_jensenDefect n = 0

/-- The horizon zero-limsup certificate for the Jensen defect. -/
def xi_horizon_purity_criterion_zero_limsup
    (D : xi_horizon_purity_criterion_data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      D.xi_horizon_purity_criterion_jensenDefect n ≤ ε

/-- The three certificate arrows making RH, vanishing defect, and zero limsup equivalent. -/
def xi_horizon_purity_criterion_statement
    (D : xi_horizon_purity_criterion_data) : Prop :=
  (xi_horizon_purity_criterion_rh D ↔
    xi_horizon_purity_criterion_vanishing_jensen_defect D) ∧
  (xi_horizon_purity_criterion_vanishing_jensen_defect D →
    xi_horizon_purity_criterion_zero_limsup D) ∧
  (xi_horizon_purity_criterion_zero_limsup D →
    xi_horizon_purity_criterion_rh D)

/-- Paper label: `thm:xi-horizon-purity-criterion`. -/
theorem paper_xi_horizon_purity_criterion
    (D : xi_horizon_purity_criterion_data) :
    xi_horizon_purity_criterion_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.xi_horizon_purity_criterion_rh_implies_vanishing,
      D.xi_horizon_purity_criterion_vanishing_implies_rh⟩
  · intro xi_horizon_purity_criterion_hvanish ε hε
    refine ⟨0, ?_⟩
    intro n _hn
    rw [xi_horizon_purity_criterion_hvanish n]
    exact le_of_lt hε
  · intro xi_horizon_purity_criterion_hlimsup
    by_contra xi_horizon_purity_criterion_hnot_rh
    obtain ⟨m, hm⟩ :=
      D.xi_horizon_purity_criterion_not_rh_has_disk_zero
        xi_horizon_purity_criterion_hnot_rh
    obtain ⟨δ, hδ_pos, hδ_liminf⟩ :=
      D.xi_horizon_purity_criterion_positive_liminf_from_disk_zero m hm
    obtain ⟨N, hN⟩ :=
      xi_horizon_purity_criterion_hlimsup (δ / 2) (by linarith)
    obtain ⟨k, hkN, hk_lower⟩ := hδ_liminf N
    have hk_upper : D.xi_horizon_purity_criterion_jensenDefect k ≤ δ / 2 := hN k hkN
    linarith

end Omega.Zeta
