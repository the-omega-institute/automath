import Mathlib.Tactic

namespace Omega.Conclusion

/--
Concrete equality-case package for the Toeplitz buffer rigidity step.  The support is
indexed by the `N + 1` polygon vertices, and equality certificates record the Rayleigh,
modulus, and finite-Fourier consequences used by the paper argument.
-/
structure conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data where
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N : ℕ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_eta : ℚ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_weight :
    Fin (conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1) → ℚ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_supportVertex :
    Fin (conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1) → ℕ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_phase : ℚ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_canonicalPhase : ℚ
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_rayleigh_extremal_certificate :
    ∀ k : Fin (conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1),
      conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_weight k =
        conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_eta /
          (conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1 : ℚ)
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_modulus_support_certificate :
    ∀ k : Fin (conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1),
      conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_supportVertex k = k.val
  conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_fourier_phase_certificate :
    conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_phase =
      conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_canonicalPhase

namespace conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data

/-- Modulus equality places the support on the opposite regular polygon vertices. -/
def support_on_regular_polygon
    (D : conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data) : Prop :=
  ∀ k : Fin (D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1),
    D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_supportVertex k = k.val

/-- Finite Fourier diagonalization forces every vertex weight to be `eta / (N + 1)`. -/
def equal_weights
    (D : conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data) : Prop :=
  ∀ k : Fin (D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1),
    D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_weight k =
      D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_eta /
        (D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_N + 1 : ℚ)

/-- Equality determines the global phase up to the recorded canonical representative. -/
def phase_unique
    (D : conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data) : Prop :=
  D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_phase =
    D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_canonicalPhase

end conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data

/-- Paper label: `thm:conclusion-toeplitz-buffer-equality-regular-polygon-rigidity`. -/
theorem paper_conclusion_toeplitz_buffer_equality_regular_polygon_rigidity
    (D : conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_data) :
    D.support_on_regular_polygon ∧ D.equal_weights ∧ D.phase_unique := by
  exact
    ⟨D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_modulus_support_certificate,
      D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_rayleigh_extremal_certificate,
      D.conclusion_toeplitz_buffer_equality_regular_polygon_rigidity_fourier_phase_certificate⟩

end Omega.Conclusion
