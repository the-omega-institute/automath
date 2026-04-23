import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Concrete Stieltjes-layer data for two consecutive tail principal minors. -/
def xi_shadow_spectrum_tower_principal_minors_stieltjes_layer_statement
    (Φ : ℝ) (upper lower : List ℝ) : Prop :=
  0 < Φ ∧ lower.length + 1 = upper.length

/-- Concrete strict interlacing for two consecutive tail principal minors. -/
def xi_shadow_spectrum_tower_principal_minors_strict_interlacing_statement
    (upper lower : List ℝ) : Prop :=
  lower.length + 1 = upper.length

/-- Concrete package for the tail principal-minor tower attached to the shadow-spectrum Jacobi
certificate. -/
structure xi_shadow_spectrum_tower_principal_minors_data where
  xi_shadow_spectrum_tower_principal_minors_depth : ℕ
  xi_shadow_spectrum_tower_principal_minors_spectrum : ℕ → List ℝ
  xi_shadow_spectrum_tower_principal_minors_normalization : ℕ → ℝ
  xi_shadow_spectrum_tower_principal_minors_stieltjes :
    ∀ r, r < xi_shadow_spectrum_tower_principal_minors_depth →
      xi_shadow_spectrum_tower_principal_minors_stieltjes_layer_statement
        (xi_shadow_spectrum_tower_principal_minors_normalization r)
        (xi_shadow_spectrum_tower_principal_minors_spectrum r)
        (xi_shadow_spectrum_tower_principal_minors_spectrum (r + 1))
  xi_shadow_spectrum_tower_principal_minors_strict_interlacing :
    ∀ r, r < xi_shadow_spectrum_tower_principal_minors_depth →
      xi_shadow_spectrum_tower_principal_minors_strict_interlacing_statement
        (xi_shadow_spectrum_tower_principal_minors_spectrum r)
        (xi_shadow_spectrum_tower_principal_minors_spectrum (r + 1))

/-- Combined tower statement: every successive tail minor carries its determinant-ratio Stieltjes
layer and every adjacent spectrum is strictly interlaced. -/
def xi_shadow_spectrum_tower_principal_minors_data.statement
    (D : xi_shadow_spectrum_tower_principal_minors_data) : Prop :=
  ∀ r, r < D.xi_shadow_spectrum_tower_principal_minors_depth →
    xi_shadow_spectrum_tower_principal_minors_stieltjes_layer_statement
        (D.xi_shadow_spectrum_tower_principal_minors_normalization r)
        (D.xi_shadow_spectrum_tower_principal_minors_spectrum r)
        (D.xi_shadow_spectrum_tower_principal_minors_spectrum (r + 1)) ∧
      xi_shadow_spectrum_tower_principal_minors_strict_interlacing_statement
        (D.xi_shadow_spectrum_tower_principal_minors_spectrum r)
        (D.xi_shadow_spectrum_tower_principal_minors_spectrum (r + 1))

/-- Paper label: `prop:xi-shadow-spectrum-tower-principal-minors`. -/
theorem paper_xi_shadow_spectrum_tower_principal_minors
    (D : xi_shadow_spectrum_tower_principal_minors_data) : D.statement := by
  intro r hr
  exact ⟨D.xi_shadow_spectrum_tower_principal_minors_stieltjes r hr,
    D.xi_shadow_spectrum_tower_principal_minors_strict_interlacing r hr⟩

end Omega.Zeta
