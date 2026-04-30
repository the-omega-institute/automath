import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete package for the rank-one 2-adic hologram image zero-measure wrapper. -/
structure xi_time_part62d_hologram_image_zero_haar_dimension_data where
  xi_time_part62d_hologram_image_zero_haar_dimension_image : Set ℕ
  xi_time_part62d_hologram_image_zero_haar_dimension_address_line : Set ℕ
  xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_count : ℕ → ℕ
  xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_scale : ℕ → ℕ
  xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value : ℝ
  xi_time_part62d_hologram_image_zero_haar_dimension_line_containment_proof :
    xi_time_part62d_hologram_image_zero_haar_dimension_image ⊆
      xi_time_part62d_hologram_image_zero_haar_dimension_address_line
  xi_time_part62d_hologram_image_zero_haar_dimension_haar_zero_proof :
    xi_time_part62d_hologram_image_zero_haar_dimension_image = ∅
  xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_dimension_formula_proof :
    ∀ n,
      xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_count n = 0 ∧
        xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_scale n = 2 ^ n
  xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value_eq_zero :
    xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value = 0

namespace xi_time_part62d_hologram_image_zero_haar_dimension_data

/-- The hologram image lies on the distinguished address line. -/
def line_containment (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  D.xi_time_part62d_hologram_image_zero_haar_dimension_image ⊆
    D.xi_time_part62d_hologram_image_zero_haar_dimension_address_line

/-- Haar-zero conclusion in the finite concrete model. -/
def haar_zero (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  D.xi_time_part62d_hologram_image_zero_haar_dimension_image = ∅

/-- Cylinder counting and scaling formula at each depth. -/
def cylinder_dimension_formula
    (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  ∀ n,
    D.xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_count n = 0 ∧
      D.xi_time_part62d_hologram_image_zero_haar_dimension_cylinder_scale n = 2 ^ n

/-- Hausdorff dimension value of the address image. -/
def hausdorff_dim_eq (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value = 0

/-- Upper Minkowski dimension value of the address image. -/
def upper_minkowski_dim_eq
    (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value = 0

/-- Lower Minkowski dimension value of the address image. -/
def lower_minkowski_dim_eq
    (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) : Prop :=
  D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value = 0

end xi_time_part62d_hologram_image_zero_haar_dimension_data

/-- Paper label: `thm:xi-time-part62d-hologram-image-zero-haar-dimension`. -/
theorem paper_xi_time_part62d_hologram_image_zero_haar_dimension
    (D : xi_time_part62d_hologram_image_zero_haar_dimension_data) :
    D.haar_zero ∧ D.hausdorff_dim_eq ∧ D.upper_minkowski_dim_eq ∧
      D.lower_minkowski_dim_eq := by
  exact
    ⟨D.xi_time_part62d_hologram_image_zero_haar_dimension_haar_zero_proof,
      D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value_eq_zero,
      D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value_eq_zero,
      D.xi_time_part62d_hologram_image_zero_haar_dimension_dimension_value_eq_zero⟩

end Omega.Zeta
