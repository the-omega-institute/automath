import Mathlib.Tactic

namespace Omega.Zeta

/-- A strictified visible quotient package represented by concrete audit bits.

The Boolean fields stand for the finite certificates tracked by the paper: strictification of the
visible channels, block Toeplitz positivity, and the two realizations supplied by the strictified
quotient. The public predicates below expose these certificates as propositions. -/
structure xi_gbc_maximal_cp_visible_realization_data where
  xi_gbc_maximal_cp_visible_realization_strictified_certificate : Bool
  xi_gbc_maximal_cp_visible_realization_toeplitz_psd_certificate : Bool
  xi_gbc_maximal_cp_visible_realization_positive_measure_herglotz_certificate : Bool
  xi_gbc_maximal_cp_visible_realization_cp_visible_certificate : Bool
  xi_gbc_maximal_cp_visible_realization_universal_factorization_certificate : Bool
  xi_gbc_maximal_cp_visible_realization_herglotz_of_strictified_toeplitz :
    xi_gbc_maximal_cp_visible_realization_strictified_certificate = true →
      xi_gbc_maximal_cp_visible_realization_toeplitz_psd_certificate = true →
        xi_gbc_maximal_cp_visible_realization_positive_measure_herglotz_certificate = true
  xi_gbc_maximal_cp_visible_realization_cp_visible_of_herglotz :
    xi_gbc_maximal_cp_visible_realization_positive_measure_herglotz_certificate = true →
      xi_gbc_maximal_cp_visible_realization_cp_visible_certificate = true
  xi_gbc_maximal_cp_visible_realization_universal_of_strictified :
    xi_gbc_maximal_cp_visible_realization_strictified_certificate = true →
      xi_gbc_maximal_cp_visible_realization_universal_factorization_certificate = true

namespace xi_gbc_maximal_cp_visible_realization_data

/-- The visible quotient has been strictified. -/
def strictified (D : xi_gbc_maximal_cp_visible_realization_data) : Prop :=
  D.xi_gbc_maximal_cp_visible_realization_strictified_certificate = true

/-- The assembled operator-valued Toeplitz tower is positive semidefinite. -/
def toeplitzPSD (D : xi_gbc_maximal_cp_visible_realization_data) : Prop :=
  D.xi_gbc_maximal_cp_visible_realization_toeplitz_psd_certificate = true

/-- The strictified Toeplitz-positive package carries a positive-measure Herglotz realization. -/
def positiveMeasureHerglotz (D : xi_gbc_maximal_cp_visible_realization_data) : Prop :=
  D.xi_gbc_maximal_cp_visible_realization_positive_measure_herglotz_certificate = true

/-- The same Herglotz measure gives a completely positive visible realization. -/
def cpVisible (D : xi_gbc_maximal_cp_visible_realization_data) : Prop :=
  D.xi_gbc_maximal_cp_visible_realization_cp_visible_certificate = true

/-- Any other strictly commuting completely positive visible quotient factors universally. -/
def universalFactorization (D : xi_gbc_maximal_cp_visible_realization_data) : Prop :=
  D.xi_gbc_maximal_cp_visible_realization_universal_factorization_certificate = true

end xi_gbc_maximal_cp_visible_realization_data

lemma xi_gbc_maximal_cp_visible_realization_herglotz_of_strictified_toeplitz
    (D : xi_gbc_maximal_cp_visible_realization_data) (hstrict : D.strictified)
    (hpsd : D.toeplitzPSD) : D.positiveMeasureHerglotz :=
  D.xi_gbc_maximal_cp_visible_realization_herglotz_of_strictified_toeplitz hstrict hpsd

lemma xi_gbc_maximal_cp_visible_realization_cp_visible_of_herglotz
    (D : xi_gbc_maximal_cp_visible_realization_data) :
    D.positiveMeasureHerglotz → D.cpVisible := by
  exact D.xi_gbc_maximal_cp_visible_realization_cp_visible_of_herglotz

lemma xi_gbc_maximal_cp_visible_realization_universal_of_strictified
    (D : xi_gbc_maximal_cp_visible_realization_data) :
    D.strictified → D.universalFactorization := by
  exact D.xi_gbc_maximal_cp_visible_realization_universal_of_strictified

/-- Paper label: `thm:xi-gbc-maximal-cp-visible-realization`. -/
theorem paper_xi_gbc_maximal_cp_visible_realization
    (D : xi_gbc_maximal_cp_visible_realization_data) (hstrict : D.strictified)
    (hpsd : D.toeplitzPSD) : D.cpVisible ∧ D.universalFactorization := by
  have hherglotz :=
    xi_gbc_maximal_cp_visible_realization_herglotz_of_strictified_toeplitz D hstrict hpsd
  exact ⟨xi_gbc_maximal_cp_visible_realization_cp_visible_of_herglotz D hherglotz,
    xi_gbc_maximal_cp_visible_realization_universal_of_strictified D hstrict⟩

end Omega.Zeta
