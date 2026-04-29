import Mathlib.Tactic

namespace Omega.Zeta

/-- Signed integral representatives for the window-`6` radial `B₃` packet.  The associated
radial point is the representative divided by its Euclidean norm. -/
abbrev xi_time_part9r_window6_radial_minimal_weyl_separator_vector := ℤ × ℤ × ℤ

def xi_time_part9r_window6_radial_minimal_weyl_separator_axial_orbit :
    List xi_time_part9r_window6_radial_minimal_weyl_separator_vector :=
  [((1 : ℤ), 0, 0), ((-1 : ℤ), 0, 0), (0, (1 : ℤ), 0), (0, (-1 : ℤ), 0),
    (0, 0, (1 : ℤ)), (0, 0, (-1 : ℤ))]

def xi_time_part9r_window6_radial_minimal_weyl_separator_diagonal_orbit :
    List xi_time_part9r_window6_radial_minimal_weyl_separator_vector :=
  [((1 : ℤ), (1 : ℤ), 0), ((1 : ℤ), (-1 : ℤ), 0), ((-1 : ℤ), (1 : ℤ), 0),
    ((-1 : ℤ), (-1 : ℤ), 0), ((1 : ℤ), 0, (1 : ℤ)),
    ((1 : ℤ), 0, (-1 : ℤ)), ((-1 : ℤ), 0, (1 : ℤ)),
    ((-1 : ℤ), 0, (-1 : ℤ)), (0, (1 : ℤ), (1 : ℤ)),
    (0, (1 : ℤ), (-1 : ℤ)), (0, (-1 : ℤ), (1 : ℤ)),
    (0, (-1 : ℤ), (-1 : ℤ))]

def xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq
    (v : xi_time_part9r_window6_radial_minimal_weyl_separator_vector) : ℚ :=
  (v.1 : ℚ) ^ 2 + (v.2.1 : ℚ) ^ 2 + (v.2.2 : ℚ) ^ 2

def xi_time_part9r_window6_radial_minimal_weyl_separator_q4
    (v : xi_time_part9r_window6_radial_minimal_weyl_separator_vector) : ℚ :=
  ((v.1 : ℚ) ^ 4 + (v.2.1 : ℚ) ^ 4 + (v.2.2 : ℚ) ^ 4) /
    xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq v ^ 2

structure xi_time_part9r_window6_radial_minimal_weyl_separator_data where
  axialOrbit : List xi_time_part9r_window6_radial_minimal_weyl_separator_vector
  diagonalOrbit : List xi_time_part9r_window6_radial_minimal_weyl_separator_vector
  axialRepresentative : xi_time_part9r_window6_radial_minimal_weyl_separator_vector
  diagonalRepresentative : xi_time_part9r_window6_radial_minimal_weyl_separator_vector
  separatorDegree : ℕ

namespace xi_time_part9r_window6_radial_minimal_weyl_separator_data

def xi_time_part9r_window6_radial_minimal_weyl_separator_orbit_package
    (D : xi_time_part9r_window6_radial_minimal_weyl_separator_data) : Prop :=
  D.axialOrbit = xi_time_part9r_window6_radial_minimal_weyl_separator_axial_orbit ∧
    D.diagonalOrbit = xi_time_part9r_window6_radial_minimal_weyl_separator_diagonal_orbit ∧
    D.axialRepresentative = ((1 : ℤ), 0, 0) ∧
    D.diagonalRepresentative = ((1 : ℤ), (1 : ℤ), 0) ∧
    D.separatorDegree = 4

def xi_time_part9r_window6_radial_minimal_weyl_separator_statement
    (D : xi_time_part9r_window6_radial_minimal_weyl_separator_data) : Prop :=
  D.axialOrbit.length = 6 ∧
    D.diagonalOrbit.length = 12 ∧
    (∀ v ∈ D.axialOrbit,
      xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq v = 1) ∧
    (∀ v ∈ D.diagonalOrbit,
      xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq v = 2) ∧
    xi_time_part9r_window6_radial_minimal_weyl_separator_q4 D.axialRepresentative = 1 ∧
    xi_time_part9r_window6_radial_minimal_weyl_separator_q4 D.diagonalRepresentative = 1 / 2 ∧
    xi_time_part9r_window6_radial_minimal_weyl_separator_q4 D.axialRepresentative ≠
      xi_time_part9r_window6_radial_minimal_weyl_separator_q4 D.diagonalRepresentative ∧
    D.separatorDegree = 4

end xi_time_part9r_window6_radial_minimal_weyl_separator_data

/-- Paper label: `prop:xi-time-part9r-window6-radial-minimal-weyl-separator`. -/
theorem paper_xi_time_part9r_window6_radial_minimal_weyl_separator
    (D : xi_time_part9r_window6_radial_minimal_weyl_separator_data)
    (hD :
      D.xi_time_part9r_window6_radial_minimal_weyl_separator_orbit_package) :
    D.xi_time_part9r_window6_radial_minimal_weyl_separator_statement := by
  rcases hD with ⟨hax, hdiag, haxrep, hdiagrep, hdeg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hax]
    native_decide
  · rw [hdiag]
    native_decide
  · intro v hv
    rw [hax] at hv
    fin_cases hv <;> norm_num [xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq]
  · intro v hv
    rw [hdiag] at hv
    fin_cases hv <;> norm_num [xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq]
  · rw [haxrep]
    norm_num [xi_time_part9r_window6_radial_minimal_weyl_separator_q4,
      xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq]
  · rw [hdiagrep]
    norm_num [xi_time_part9r_window6_radial_minimal_weyl_separator_q4,
      xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq]
  · rw [haxrep, hdiagrep]
    norm_num [xi_time_part9r_window6_radial_minimal_weyl_separator_q4,
      xi_time_part9r_window6_radial_minimal_weyl_separator_norm_sq]
  · exact hdeg

end Omega.Zeta
