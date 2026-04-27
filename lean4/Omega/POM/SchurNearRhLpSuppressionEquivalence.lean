import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite-channel package for comparing the near-RH radius bound with `L^p`
suppression.  The identity field records that every packaged `L^p` exponent is the same Schur
limsup exponent on the finite channel set. -/
structure pom_schur_near_rh_lp_suppression_equivalence_data where
  pom_schur_near_rh_lp_suppression_equivalence_channel_count : ℕ
  pom_schur_near_rh_lp_suppression_equivalence_rh_radius : ℝ
  pom_schur_near_rh_lp_suppression_equivalence_schur_limsup :
    Fin pom_schur_near_rh_lp_suppression_equivalence_channel_count → ℝ
  pom_schur_near_rh_lp_suppression_equivalence_lp_limsup :
    ℝ → Fin pom_schur_near_rh_lp_suppression_equivalence_channel_count → ℝ
  pom_schur_near_rh_lp_suppression_equivalence_limsup_identity :
    ∀ (p : ℝ)
      (i : Fin pom_schur_near_rh_lp_suppression_equivalence_channel_count),
        pom_schur_near_rh_lp_suppression_equivalence_lp_limsup p i =
          pom_schur_near_rh_lp_suppression_equivalence_schur_limsup i

namespace pom_schur_near_rh_lp_suppression_equivalence_data

/-- The near-RH finite-channel square-root radius bound. -/
def pom_schur_near_rh_lp_suppression_equivalence_near_rh_bound
    (D : pom_schur_near_rh_lp_suppression_equivalence_data) : Prop :=
  ∀ i : Fin D.pom_schur_near_rh_lp_suppression_equivalence_channel_count,
    D.pom_schur_near_rh_lp_suppression_equivalence_schur_limsup i ≤
      D.pom_schur_near_rh_lp_suppression_equivalence_rh_radius

/-- Uniform `L^p` suppression for every finite channel and every `p ≥ 1`. -/
def pom_schur_near_rh_lp_suppression_equivalence_lp_suppressed
    (D : pom_schur_near_rh_lp_suppression_equivalence_data) : Prop :=
  ∀ p : ℝ, 1 ≤ p →
    ∀ i : Fin D.pom_schur_near_rh_lp_suppression_equivalence_channel_count,
      D.pom_schur_near_rh_lp_suppression_equivalence_lp_limsup p i ≤
        D.pom_schur_near_rh_lp_suppression_equivalence_rh_radius

end pom_schur_near_rh_lp_suppression_equivalence_data

/-- Concrete statement for `cor:pom-schur-near-rh-lp-suppression-equivalence`. -/
def pom_schur_near_rh_lp_suppression_equivalence_statement
    (D : pom_schur_near_rh_lp_suppression_equivalence_data) : Prop :=
  D.pom_schur_near_rh_lp_suppression_equivalence_near_rh_bound ↔
    D.pom_schur_near_rh_lp_suppression_equivalence_lp_suppressed

/-- Paper label: `cor:pom-schur-near-rh-lp-suppression-equivalence`. -/
theorem paper_pom_schur_near_rh_lp_suppression_equivalence
    (D : pom_schur_near_rh_lp_suppression_equivalence_data) :
    pom_schur_near_rh_lp_suppression_equivalence_statement D := by
  constructor
  · intro hnear p _ i
    rw [D.pom_schur_near_rh_lp_suppression_equivalence_limsup_identity p i]
    exact hnear i
  · intro hlp i
    have h := hlp 1 (by norm_num) i
    rwa [D.pom_schur_near_rh_lp_suppression_equivalence_limsup_identity 1 i] at h

end Omega.POM
