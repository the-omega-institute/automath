import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete two-atom data for the bin-fold capacity size-bias law. -/
structure xi_binfold_capacity_size_bias_uniform_law_data where
  xi_binfold_capacity_size_bias_uniform_law_marker : ℕ := 0

namespace xi_binfold_capacity_size_bias_uniform_law_data

/-- The golden ratio used by the two-atom law. -/
def xi_binfold_capacity_size_bias_uniform_law_phi : ℝ :=
  Real.goldenRatio

/-- The two atoms: `true` is the atom at `1`, `false` is the atom at `φ⁻¹`. -/
def xi_binfold_capacity_size_bias_uniform_law_atom
    (_D : xi_binfold_capacity_size_bias_uniform_law_data) : Bool → ℝ
  | true => 1
  | false => 1 / xi_binfold_capacity_size_bias_uniform_law_phi

/-- The limiting uniform two-point law. -/
def xi_binfold_capacity_size_bias_uniform_law_uniformMass
    (_D : xi_binfold_capacity_size_bias_uniform_law_data) : Bool → ℝ
  | true => 1 / xi_binfold_capacity_size_bias_uniform_law_phi
  | false => 1 / xi_binfold_capacity_size_bias_uniform_law_phi ^ 2

/-- Expectation of the limiting uniform two-point law. -/
def xi_binfold_capacity_size_bias_uniform_law_expectation
    (D : xi_binfold_capacity_size_bias_uniform_law_data) : ℝ :=
  D.xi_binfold_capacity_size_bias_uniform_law_uniformMass true *
      D.xi_binfold_capacity_size_bias_uniform_law_atom true +
    D.xi_binfold_capacity_size_bias_uniform_law_uniformMass false *
      D.xi_binfold_capacity_size_bias_uniform_law_atom false

/-- Size-biased mass at either atom. -/
def xi_binfold_capacity_size_bias_uniform_law_sizeBiasedMass
    (D : xi_binfold_capacity_size_bias_uniform_law_data) (b : Bool) : ℝ :=
  D.xi_binfold_capacity_size_bias_uniform_law_atom b *
      D.xi_binfold_capacity_size_bias_uniform_law_uniformMass b /
    D.xi_binfold_capacity_size_bias_uniform_law_expectation

/-- The uniform weighted minimum expectation. -/
def xi_binfold_capacity_size_bias_uniform_law_weightedMin
    (D : xi_binfold_capacity_size_bias_uniform_law_data) (s : ℝ) : ℝ :=
  D.xi_binfold_capacity_size_bias_uniform_law_uniformMass true *
      min (D.xi_binfold_capacity_size_bias_uniform_law_atom true) s +
    D.xi_binfold_capacity_size_bias_uniform_law_uniformMass false *
      min (D.xi_binfold_capacity_size_bias_uniform_law_atom false) s

/-- The capacity functional represented as a scaled weighted minimum expectation. -/
def xi_binfold_capacity_size_bias_uniform_law_capacity
    (D : xi_binfold_capacity_size_bias_uniform_law_data) (s : ℝ) : ℝ :=
  xi_binfold_capacity_size_bias_uniform_law_phi ^ 2 / Real.sqrt 5 *
    D.xi_binfold_capacity_size_bias_uniform_law_weightedMin s

/-- Statement of the bin-fold capacity size-bias uniform law. -/
def xi_binfold_capacity_size_bias_uniform_law_statement
    (D : xi_binfold_capacity_size_bias_uniform_law_data) : Prop :=
  D.xi_binfold_capacity_size_bias_uniform_law_expectation =
      Real.sqrt 5 / xi_binfold_capacity_size_bias_uniform_law_phi ^ 2 ∧
    D.xi_binfold_capacity_size_bias_uniform_law_sizeBiasedMass true =
      xi_binfold_capacity_size_bias_uniform_law_phi / Real.sqrt 5 ∧
    D.xi_binfold_capacity_size_bias_uniform_law_sizeBiasedMass false =
      1 / (xi_binfold_capacity_size_bias_uniform_law_phi * Real.sqrt 5) ∧
    ∀ s : ℝ,
      D.xi_binfold_capacity_size_bias_uniform_law_capacity s =
        xi_binfold_capacity_size_bias_uniform_law_phi ^ 2 / Real.sqrt 5 *
          D.xi_binfold_capacity_size_bias_uniform_law_weightedMin s

end xi_binfold_capacity_size_bias_uniform_law_data

open xi_binfold_capacity_size_bias_uniform_law_data

/-- Paper label: `thm:xi-binfold-capacity-size-bias-uniform-law`. -/
theorem paper_xi_binfold_capacity_size_bias_uniform_law
    (D : xi_binfold_capacity_size_bias_uniform_law_data) :
    xi_binfold_capacity_size_bias_uniform_law_statement D := by
  dsimp [xi_binfold_capacity_size_bias_uniform_law_statement]
  set φ : ℝ := xi_binfold_capacity_size_bias_uniform_law_phi
  have hφ_ne : φ ≠ 0 := by
    simpa [φ, xi_binfold_capacity_size_bias_uniform_law_phi] using
      Real.goldenRatio_ne_zero
  have hφ_sq : φ ^ 2 = φ + 1 := by
    simp [φ, xi_binfold_capacity_size_bias_uniform_law_phi,
      Real.goldenRatio_sq]
  have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
    have hφ_def : φ = (1 + Real.sqrt 5) / 2 := by
      simp [φ, xi_binfold_capacity_size_bias_uniform_law_phi, Real.goldenRatio]
    nlinarith
  have hsqrt_ne : Real.sqrt 5 ≠ 0 := by positivity
  have hE :
      D.xi_binfold_capacity_size_bias_uniform_law_expectation =
        Real.sqrt 5 / φ ^ 2 := by
    have hsum :
        D.xi_binfold_capacity_size_bias_uniform_law_expectation =
          1 / φ + 1 / φ ^ 3 := by
      dsimp [xi_binfold_capacity_size_bias_uniform_law_expectation,
        xi_binfold_capacity_size_bias_uniform_law_uniformMass,
        xi_binfold_capacity_size_bias_uniform_law_atom, φ]
      ring_nf
    rw [hsum]
    field_simp [hφ_ne]
    nlinarith [hφ_sq, hsqrt]
  refine ⟨hE, ?_, ?_, ?_⟩
  · rw [xi_binfold_capacity_size_bias_uniform_law_sizeBiasedMass, hE]
    dsimp [xi_binfold_capacity_size_bias_uniform_law_uniformMass,
      xi_binfold_capacity_size_bias_uniform_law_atom, φ]
    field_simp [hφ_ne, hsqrt_ne]
  · rw [xi_binfold_capacity_size_bias_uniform_law_sizeBiasedMass, hE]
    dsimp [xi_binfold_capacity_size_bias_uniform_law_uniformMass,
      xi_binfold_capacity_size_bias_uniform_law_atom, φ]
    field_simp [hφ_ne, hsqrt_ne]
  · intro s
    rfl

end

end Omega.Zeta
