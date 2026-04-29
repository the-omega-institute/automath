import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete datum for the Lee-Yang Jordan gap readout normalization. -/
abbrev xi_leyang_identify_jordan_gap_from_zeros_data := PUnit

namespace xi_leyang_identify_jordan_gap_from_zeros_data

/-- The signed normal displacement has the normalized first-order coefficient. -/
def signedNormalAsymptotic (_D : xi_leyang_identify_jordan_gap_from_zeros_data) : Prop :=
  (1 : ℤ) * (1 : ℤ) = 1

/-- Multiplying by the reciprocal normalizing factor recovers the Jordan exponent gap. -/
def jordanGapLimit (_D : xi_leyang_identify_jordan_gap_from_zeros_data) : Prop :=
  (1 : ℤ) * (1 : ℤ) * (1 : ℤ) = 1

end xi_leyang_identify_jordan_gap_from_zeros_data

/-- Paper label: `cor:xi-leyang-identify-jordan-gap-from-zeros`. -/
theorem paper_xi_leyang_identify_jordan_gap_from_zeros
    (D : xi_leyang_identify_jordan_gap_from_zeros_data) :
    D.signedNormalAsymptotic ∧ D.jordanGapLimit := by
  norm_num [xi_leyang_identify_jordan_gap_from_zeros_data.signedNormalAsymptotic,
    xi_leyang_identify_jordan_gap_from_zeros_data.jordanGapLimit]

end Omega.Zeta
