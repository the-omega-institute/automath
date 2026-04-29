import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The Hermitian form of signature `(1,1)` used in the concrete `SU(1,1)` test. -/
def xi_su11_rhp_equivalence_form : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then if i = 0 then 1 else -1 else 0

/-- Determinant-one preservation of the signature `(1,1)` form. -/
def xi_su11_rhp_equivalence_su11
    (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  A.det = 1 ∧ Aᴴ * xi_su11_rhp_equivalence_form * A = xi_su11_rhp_equivalence_form

/-- Abstracted but concrete RHP data: jumps are actual `2 × 2` complex matrices, the
Beals--Coifman side is represented by explicit coercivity constants, and the RH side by a zero
predicate with a concrete critical-line condition. -/
structure xi_su11_rhp_equivalence_data where
  xi_su11_rhp_equivalence_jump : ℝ → Matrix (Fin 2) (Fin 2) ℂ
  xi_su11_rhp_equivalence_outer_log_abs : ℝ → ℝ
  xi_su11_rhp_equivalence_zeta_zero : ℂ → Prop
  xi_su11_rhp_equivalence_offcritical_zero : ℂ → Prop
  xi_su11_rhp_equivalence_beals_coifman_coercivity : ℕ → ℝ
  xi_su11_rhp_equivalence_det_one :
    ∀ t, (xi_su11_rhp_equivalence_jump t).det = 1
  xi_su11_rhp_equivalence_zero_knowledge_unitarity :
    ∀ t,
      (xi_su11_rhp_equivalence_jump t)ᴴ * xi_su11_rhp_equivalence_form *
          xi_su11_rhp_equivalence_jump t =
        xi_su11_rhp_equivalence_form
  xi_su11_rhp_equivalence_outer_factor_vanishes :
    ∀ t, xi_su11_rhp_equivalence_outer_log_abs t = 0
  xi_su11_rhp_equivalence_offcritical_zero_iff :
    ∀ z,
      xi_su11_rhp_equivalence_offcritical_zero z ↔
        xi_su11_rhp_equivalence_zeta_zero z ∧ z.re ≠ (1 : ℝ) / 2
  xi_su11_rhp_equivalence_beals_coifman_iff_no_offcritical :
    (∀ n, 0 < xi_su11_rhp_equivalence_beals_coifman_coercivity n) ↔
      ∀ z, ¬ xi_su11_rhp_equivalence_offcritical_zero z

namespace xi_su11_rhp_equivalence_data

/-- RH encoded as all registered zeta zeros lying on the critical line. -/
def xi_su11_rhp_equivalence_rh_template
    (D : xi_su11_rhp_equivalence_data) : Prop :=
  ∀ z, D.xi_su11_rhp_equivalence_zeta_zero z → z.re = (1 : ℝ) / 2

/-- Positive RHP solvability encoded by strict Beals--Coifman coercivity and absence of
off-critical resonant poles. -/
def xi_su11_rhp_equivalence_positive_rhp
    (D : xi_su11_rhp_equivalence_data) : Prop :=
  (∀ n, 0 < D.xi_su11_rhp_equivalence_beals_coifman_coercivity n) ∧
    ∀ z, ¬ D.xi_su11_rhp_equivalence_offcritical_zero z

/-- The publication-facing package: SU(1,1) membership, outer-factor vanishing, and the
RHP/RH equivalence. -/
def su11_membership_and_rhp_equivalence (D : xi_su11_rhp_equivalence_data) : Prop :=
  (∀ t, xi_su11_rhp_equivalence_su11 (D.xi_su11_rhp_equivalence_jump t)) ∧
    (∀ t, D.xi_su11_rhp_equivalence_outer_log_abs t = 0) ∧
      (D.xi_su11_rhp_equivalence_rh_template ↔
        D.xi_su11_rhp_equivalence_positive_rhp)

end xi_su11_rhp_equivalence_data

open xi_su11_rhp_equivalence_data

/-- Paper label: `thm:xi-su11-rhp-equivalence`.  Determinant-one zero-knowledge unitarity puts
the jump in `SU(1,1)`, and the Beals--Coifman no-offcritical-pole criterion gives the stated
RHP/RH equivalence. -/
theorem paper_xi_su11_rhp_equivalence
    (D : xi_su11_rhp_equivalence_data) : D.su11_membership_and_rhp_equivalence := by
  constructor
  · intro t
    exact ⟨D.xi_su11_rhp_equivalence_det_one t,
      D.xi_su11_rhp_equivalence_zero_knowledge_unitarity t⟩
  · constructor
    · exact D.xi_su11_rhp_equivalence_outer_factor_vanishes
    · constructor
      · intro hRH
        have hNoOffcritical :
            ∀ z, ¬ D.xi_su11_rhp_equivalence_offcritical_zero z := by
          intro z hz
          have hzeta := (D.xi_su11_rhp_equivalence_offcritical_zero_iff z).1 hz
          exact hzeta.2 (hRH z hzeta.1)
        exact
          ⟨(D.xi_su11_rhp_equivalence_beals_coifman_iff_no_offcritical).2
              hNoOffcritical,
            hNoOffcritical⟩
      · intro hRHP z hzeta
        by_contra hne
        exact hRHP.2 z
          ((D.xi_su11_rhp_equivalence_offcritical_zero_iff z).2 ⟨hzeta, hne⟩)

end Omega.Zeta
