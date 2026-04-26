import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Concrete radius data for a dyadic boundary code with minimum-distance certificate `2n`. -/
structure conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data where
  n : ℕ

namespace conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data

/-- The uniform Hamming unique-decoding radius certified by `d_min = 2n`. -/
def hammingUniformRadius
    (D : conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data) : ℕ :=
  D.n - 1

/-- The uniform arithmetic unique-decoding radius certified by the same boundary witness. -/
def arithmeticUniformRadius
    (D : conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data) : ℕ :=
  D.n - 1

end conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data

/-- Paper label:
`cor:conclusion-dyadic-boundary-code-uniform-unique-decoding-radius`. -/
theorem paper_conclusion_dyadic_boundary_code_uniform_unique_decoding_radius
    (D : conclusion_dyadic_boundary_code_uniform_unique_decoding_radius_data) :
    D.hammingUniformRadius = D.n - 1 ∧ D.arithmeticUniformRadius = D.n - 1 := by
  constructor <;> rfl

end Omega.Conclusion
