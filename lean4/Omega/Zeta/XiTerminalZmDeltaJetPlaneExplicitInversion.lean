import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete input coordinates for the delta-jet plane inversion chart. -/
structure xi_terminal_zm_delta_jet_plane_explicit_inversion_data where
  y : ℚ
  T : ℚ

/-- The denominator in the explicit inverse chart. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_Q (y T : ℚ) : ℚ :=
  8192 * y ^ 4 + 5888 * y ^ 3 - 3680 * y ^ 2 - 2848 * y + 152 - 93 * T

/-- The numerator in the explicit inverse chart. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_N (y T : ℚ) : ℚ :=
  64 * T ^ 3 + 512 * T ^ 2 * y ^ 2 + 528 * T ^ 2 * y - 219 * T ^ 2 +
    1024 * T * y ^ 3 - 288 * T * y ^ 2 - 1154 * T * y - 131 * T -
      3584 * y ^ 4 - 2928 * y ^ 3 - 415 * y ^ 2 - 929 * y + 152

/-- The cleared plane relation used by the inverse chart. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_F_delta (y T : ℚ) : ℚ :=
  let Q := xi_terminal_zm_delta_jet_plane_explicit_inversion_Q y T
  let N := xi_terminal_zm_delta_jet_plane_explicit_inversion_N y T
  Q ^ 3 * (T + 1) - 3 * N ^ 2 * Q - 4 * N * ((y + 1 / 2) * Q ^ 2 - N ^ 2)

/-- The inverse `X` coordinate. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_X (y T : ℚ) : ℚ :=
  xi_terminal_zm_delta_jet_plane_explicit_inversion_N y T /
    xi_terminal_zm_delta_jet_plane_explicit_inversion_Q y T

/-- The inverse `Y` coordinate. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_Y (y T : ℚ) : ℚ :=
  y - xi_terminal_zm_delta_jet_plane_explicit_inversion_X y T ^ 2 + 1 / 2

/-- The two inverse identities on the nonzero-denominator chart. -/
def xi_terminal_zm_delta_jet_plane_explicit_inversion_statement
    (D : xi_terminal_zm_delta_jet_plane_explicit_inversion_data) : Prop :=
  xi_terminal_zm_delta_jet_plane_explicit_inversion_Q D.y D.T ≠ 0 →
    xi_terminal_zm_delta_jet_plane_explicit_inversion_F_delta D.y D.T = 0 →
      D.y =
          xi_terminal_zm_delta_jet_plane_explicit_inversion_X D.y D.T ^ 2 +
            xi_terminal_zm_delta_jet_plane_explicit_inversion_Y D.y D.T - 1 / 2 ∧
        D.T =
          4 * xi_terminal_zm_delta_jet_plane_explicit_inversion_X D.y D.T *
              xi_terminal_zm_delta_jet_plane_explicit_inversion_Y D.y D.T +
            3 * xi_terminal_zm_delta_jet_plane_explicit_inversion_X D.y D.T ^ 2 - 1

/-- Paper label: `prop:xi-terminal-zm-delta-jet-plane-explicit-inversion`. -/
theorem paper_xi_terminal_zm_delta_jet_plane_explicit_inversion
    (D : xi_terminal_zm_delta_jet_plane_explicit_inversion_data) :
    xi_terminal_zm_delta_jet_plane_explicit_inversion_statement D := by
  intro hQ hF
  constructor
  · rw [xi_terminal_zm_delta_jet_plane_explicit_inversion_Y]
    ring
  · let Q := xi_terminal_zm_delta_jet_plane_explicit_inversion_Q D.y D.T
    let N := xi_terminal_zm_delta_jet_plane_explicit_inversion_N D.y D.T
    have hF' :
        Q ^ 3 * (D.T + 1) - 3 * N ^ 2 * Q -
            4 * N * ((D.y + 1 / 2) * Q ^ 2 - N ^ 2) =
          0 := by
      simpa [xi_terminal_zm_delta_jet_plane_explicit_inversion_F_delta, Q, N] using hF
    have hQ' : Q ≠ 0 := by
      simpa [Q] using hQ
    rw [xi_terminal_zm_delta_jet_plane_explicit_inversion_X,
      xi_terminal_zm_delta_jet_plane_explicit_inversion_Y]
    change
      D.T =
        4 * (N / Q) * (D.y - (N / Q) ^ 2 + 1 / 2) + 3 * (N / Q) ^ 2 - 1
    field_simp [hQ']
    nlinarith [hF']

end Omega.Zeta
