import Mathlib.Tactic

namespace Omega.Zeta

abbrev xi_time_part9r_window6_b3c3_root_polytopes_vector := ℤ × ℤ × ℤ

def xi_time_part9r_window6_b3c3_root_polytopes_b3_vertices :
    List xi_time_part9r_window6_b3c3_root_polytopes_vector :=
  [((1 : ℤ), (1 : ℤ), 0), ((1 : ℤ), (-1 : ℤ), 0), ((-1 : ℤ), (1 : ℤ), 0),
    ((-1 : ℤ), (-1 : ℤ), 0), ((1 : ℤ), 0, (1 : ℤ)),
    ((1 : ℤ), 0, (-1 : ℤ)), ((-1 : ℤ), 0, (1 : ℤ)),
    ((-1 : ℤ), 0, (-1 : ℤ)), (0, (1 : ℤ), (1 : ℤ)),
    (0, (1 : ℤ), (-1 : ℤ)), (0, (-1 : ℤ), (1 : ℤ)),
    (0, (-1 : ℤ), (-1 : ℤ))]

def xi_time_part9r_window6_b3c3_root_polytopes_b3_face_centers :
    List xi_time_part9r_window6_b3c3_root_polytopes_vector :=
  [((1 : ℤ), 0, 0), ((-1 : ℤ), 0, 0), (0, (1 : ℤ), 0), (0, (-1 : ℤ), 0),
    (0, 0, (1 : ℤ)), (0, 0, (-1 : ℤ))]

def xi_time_part9r_window6_b3c3_root_polytopes_c3_vertices :
    List xi_time_part9r_window6_b3c3_root_polytopes_vector :=
  [((2 : ℤ), 0, 0), ((-2 : ℤ), 0, 0), (0, (2 : ℤ), 0), (0, (-2 : ℤ), 0),
    (0, 0, (2 : ℤ)), (0, 0, (-2 : ℤ))]

def xi_time_part9r_window6_b3c3_root_polytopes_c3_edge_midpoints :
    List xi_time_part9r_window6_b3c3_root_polytopes_vector :=
  xi_time_part9r_window6_b3c3_root_polytopes_b3_vertices

def xi_time_part9r_window6_b3c3_root_polytopes_b3_first_octant_volume : ℚ :=
  1 - 1 / 6

def xi_time_part9r_window6_b3c3_root_polytopes_b3_volume : ℚ :=
  8 * xi_time_part9r_window6_b3c3_root_polytopes_b3_first_octant_volume

def xi_time_part9r_window6_b3c3_root_polytopes_c3_first_octant_volume : ℚ :=
  2 ^ 3 / 6

def xi_time_part9r_window6_b3c3_root_polytopes_c3_volume : ℚ :=
  8 * xi_time_part9r_window6_b3c3_root_polytopes_c3_first_octant_volume

structure xi_time_part9r_window6_b3c3_root_polytopes_data where
  b3Vertices : List xi_time_part9r_window6_b3c3_root_polytopes_vector
  b3FaceCenters : List xi_time_part9r_window6_b3c3_root_polytopes_vector
  c3Vertices : List xi_time_part9r_window6_b3c3_root_polytopes_vector
  c3EdgeMidpoints : List xi_time_part9r_window6_b3c3_root_polytopes_vector
  b3Volume : ℚ
  c3Volume : ℚ

namespace xi_time_part9r_window6_b3c3_root_polytopes_data

def xi_time_part9r_window6_b3c3_root_polytopes_polytope_package
    (D : xi_time_part9r_window6_b3c3_root_polytopes_data) : Prop :=
  D.b3Vertices = xi_time_part9r_window6_b3c3_root_polytopes_b3_vertices ∧
    D.b3FaceCenters = xi_time_part9r_window6_b3c3_root_polytopes_b3_face_centers ∧
    D.c3Vertices = xi_time_part9r_window6_b3c3_root_polytopes_c3_vertices ∧
    D.c3EdgeMidpoints = xi_time_part9r_window6_b3c3_root_polytopes_c3_edge_midpoints ∧
    D.b3Volume = xi_time_part9r_window6_b3c3_root_polytopes_b3_volume ∧
    D.c3Volume = xi_time_part9r_window6_b3c3_root_polytopes_c3_volume

def xi_time_part9r_window6_b3c3_root_polytopes_statement
    (D : xi_time_part9r_window6_b3c3_root_polytopes_data) : Prop :=
  D.b3Vertices.length = 12 ∧
    D.b3FaceCenters.length = 6 ∧
    D.c3Vertices.length = 6 ∧
    D.c3EdgeMidpoints.length = 12 ∧
    xi_time_part9r_window6_b3c3_root_polytopes_b3_first_octant_volume = 5 / 6 ∧
    D.b3Volume = 20 / 3 ∧
    xi_time_part9r_window6_b3c3_root_polytopes_c3_first_octant_volume = 4 / 3 ∧
    D.c3Volume = 32 / 3

end xi_time_part9r_window6_b3c3_root_polytopes_data

/-- Paper label: `thm:xi-time-part9r-window6-b3c3-root-polytopes`. -/
theorem paper_xi_time_part9r_window6_b3c3_root_polytopes
    (D : xi_time_part9r_window6_b3c3_root_polytopes_data)
    (hD : D.xi_time_part9r_window6_b3c3_root_polytopes_polytope_package) :
    D.xi_time_part9r_window6_b3c3_root_polytopes_statement := by
  rcases hD with ⟨hb3, hb3c, hc3, hc3m, hb3vol, hc3vol⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb3]
    native_decide
  · rw [hb3c]
    native_decide
  · rw [hc3]
    native_decide
  · rw [hc3m]
    native_decide
  · norm_num [xi_time_part9r_window6_b3c3_root_polytopes_b3_first_octant_volume]
  · rw [hb3vol]
    norm_num [xi_time_part9r_window6_b3c3_root_polytopes_b3_volume,
      xi_time_part9r_window6_b3c3_root_polytopes_b3_first_octant_volume]
  · norm_num [xi_time_part9r_window6_b3c3_root_polytopes_c3_first_octant_volume]
  · rw [hc3vol]
    norm_num [xi_time_part9r_window6_b3c3_root_polytopes_c3_volume,
      xi_time_part9r_window6_b3c3_root_polytopes_c3_first_octant_volume]

end Omega.Zeta
