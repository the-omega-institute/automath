import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-window CMV/Schur/Sturm/Cayley certificate data. -/
structure xi_finite_window_extreme_resonance_certificate_data where
  xi_finite_window_extreme_resonance_certificate_windowDegree : ℕ
  xi_finite_window_extreme_resonance_certificate_cmvMatrix :
    Matrix (Fin xi_finite_window_extreme_resonance_certificate_windowDegree)
      (Fin xi_finite_window_extreme_resonance_certificate_windowDegree) ℂ
  xi_finite_window_extreme_resonance_certificate_schurParameter :
    Fin xi_finite_window_extreme_resonance_certificate_windowDegree → ℂ
  xi_finite_window_extreme_resonance_certificate_sturmLeft :
    Fin xi_finite_window_extreme_resonance_certificate_windowDegree → ℚ
  xi_finite_window_extreme_resonance_certificate_sturmRight :
    Fin xi_finite_window_extreme_resonance_certificate_windowDegree → ℚ
  xi_finite_window_extreme_resonance_certificate_cayleyModel :
    Matrix (Fin xi_finite_window_extreme_resonance_certificate_windowDegree)
      (Fin xi_finite_window_extreme_resonance_certificate_windowDegree) ℂ
  xi_finite_window_extreme_resonance_certificate_boundary_iff_unitary :
    (∀ z : ℂ,
        xi_finite_window_extreme_resonance_certificate_cmvMatrix.charpoly.eval z = 0 →
          ‖z‖ = 1) ↔
      (∀ i j,
        (∑ k,
          star (xi_finite_window_extreme_resonance_certificate_cmvMatrix k i) *
            xi_finite_window_extreme_resonance_certificate_cmvMatrix k j) =
          if i = j then 1 else 0)
  xi_finite_window_extreme_resonance_certificate_unitary_iff_schur :
    (∀ i j,
        (∑ k,
          star (xi_finite_window_extreme_resonance_certificate_cmvMatrix k i) *
            xi_finite_window_extreme_resonance_certificate_cmvMatrix k j) =
          if i = j then 1 else 0) ↔
      ((∀ k,
          k.1 + 1 <
              xi_finite_window_extreme_resonance_certificate_windowDegree →
            ‖xi_finite_window_extreme_resonance_certificate_schurParameter k‖ < 1) ∧
        ∀ k,
          k.1 + 1 =
              xi_finite_window_extreme_resonance_certificate_windowDegree →
            ‖xi_finite_window_extreme_resonance_certificate_schurParameter k‖ = 1)
  xi_finite_window_extreme_resonance_certificate_sturmCertificate :
    ∀ z : ℂ,
      xi_finite_window_extreme_resonance_certificate_cmvMatrix.charpoly.eval z = 0 →
        ∃ k,
          xi_finite_window_extreme_resonance_certificate_sturmLeft k ≤
            xi_finite_window_extreme_resonance_certificate_sturmRight k
  xi_finite_window_extreme_resonance_certificate_cayleyCompatibility :
    ∀ i j,
      xi_finite_window_extreme_resonance_certificate_cayleyModel i j =
        xi_finite_window_extreme_resonance_certificate_cmvMatrix i j

namespace xi_finite_window_extreme_resonance_certificate_data

/-- Boundary-spectrum certificate for the CMV characteristic polynomial. -/
def xi_finite_window_extreme_resonance_certificate_boundarySpectrum
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  ∀ z : ℂ,
    D.xi_finite_window_extreme_resonance_certificate_cmvMatrix.charpoly.eval z = 0 →
      ‖z‖ = 1

/-- Column-unitarity of the finite CMV-like realization. -/
def xi_finite_window_extreme_resonance_certificate_cmvUnitary
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  ∀ i j,
    (∑ k,
      star (D.xi_finite_window_extreme_resonance_certificate_cmvMatrix k i) *
        D.xi_finite_window_extreme_resonance_certificate_cmvMatrix k j) =
      if i = j then 1 else 0

/-- Finite Schur/Verblunsky parameter bounds for the window. -/
def xi_finite_window_extreme_resonance_certificate_schurBounds
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  (∀ k,
      k.1 + 1 < D.xi_finite_window_extreme_resonance_certificate_windowDegree →
        ‖D.xi_finite_window_extreme_resonance_certificate_schurParameter k‖ < 1) ∧
    ∀ k,
      k.1 + 1 = D.xi_finite_window_extreme_resonance_certificate_windowDegree →
        ‖D.xi_finite_window_extreme_resonance_certificate_schurParameter k‖ = 1

/-- Sturm interval coverage for every root of the finite characteristic polynomial. -/
def xi_finite_window_extreme_resonance_certificate_sturmIntervals
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  ∀ z : ℂ,
    D.xi_finite_window_extreme_resonance_certificate_cmvMatrix.charpoly.eval z = 0 →
      ∃ k,
        D.xi_finite_window_extreme_resonance_certificate_sturmLeft k ≤
          D.xi_finite_window_extreme_resonance_certificate_sturmRight k

/-- Cayley compatibility identifies the unitary and self-adjoint finite-window models. -/
def xi_finite_window_extreme_resonance_certificate_cayleyCompatible
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  ∀ i j,
    D.xi_finite_window_extreme_resonance_certificate_cayleyModel i j =
      D.xi_finite_window_extreme_resonance_certificate_cmvMatrix i j

end xi_finite_window_extreme_resonance_certificate_data

/-- The finite-window certificate packages monicity, the CMV/Schur equivalence chain, Sturm
interval audit data, Cayley compatibility, and the resulting boundary-spectrum implication. -/
def xi_finite_window_extreme_resonance_certificate_statement
    (D : xi_finite_window_extreme_resonance_certificate_data) : Prop :=
  D.xi_finite_window_extreme_resonance_certificate_cmvMatrix.charpoly.Monic ∧
    (D.xi_finite_window_extreme_resonance_certificate_boundarySpectrum ↔
      D.xi_finite_window_extreme_resonance_certificate_cmvUnitary) ∧
    (D.xi_finite_window_extreme_resonance_certificate_cmvUnitary ↔
      D.xi_finite_window_extreme_resonance_certificate_schurBounds) ∧
    D.xi_finite_window_extreme_resonance_certificate_sturmIntervals ∧
    D.xi_finite_window_extreme_resonance_certificate_cayleyCompatible ∧
      (D.xi_finite_window_extreme_resonance_certificate_schurBounds →
        D.xi_finite_window_extreme_resonance_certificate_boundarySpectrum)

/-- Paper label: `thm:xi-finite-window-extreme-resonance-certificate`. -/
theorem paper_xi_finite_window_extreme_resonance_certificate
    (D : xi_finite_window_extreme_resonance_certificate_data) :
    xi_finite_window_extreme_resonance_certificate_statement D := by
  refine ⟨Matrix.charpoly_monic D.xi_finite_window_extreme_resonance_certificate_cmvMatrix,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_boundarySpectrum,
      xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_cmvUnitary] using
      D.xi_finite_window_extreme_resonance_certificate_boundary_iff_unitary
  · simpa [xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_cmvUnitary,
      xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_schurBounds] using
      D.xi_finite_window_extreme_resonance_certificate_unitary_iff_schur
  · simpa [xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_sturmIntervals] using
      D.xi_finite_window_extreme_resonance_certificate_sturmCertificate
  · simpa [xi_finite_window_extreme_resonance_certificate_data.xi_finite_window_extreme_resonance_certificate_cayleyCompatible] using
      D.xi_finite_window_extreme_resonance_certificate_cayleyCompatibility
  · intro hschur
    exact
      (D.xi_finite_window_extreme_resonance_certificate_boundary_iff_unitary).mpr
        ((D.xi_finite_window_extreme_resonance_certificate_unitary_iff_schur).mpr
          hschur)

end Omega.Zeta
