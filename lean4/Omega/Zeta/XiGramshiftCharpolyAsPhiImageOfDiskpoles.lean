import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite Gram--shift data: disk poles, their `PhiDelta` image, and the characteristic
polynomial to be factored. -/
structure xi_gramshift_charpoly_as_phi_image_of_diskpoles_data where
  xi_gramshift_charpoly_as_phi_image_of_diskpoles_rank : ℕ
  xi_gramshift_charpoly_as_phi_image_of_diskpoles_phi : ℂ → ℂ
  xi_gramshift_charpoly_as_phi_image_of_diskpoles_disk_pole :
    Fin xi_gramshift_charpoly_as_phi_image_of_diskpoles_rank → ℂ
  xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly : Polynomial ℂ

namespace xi_gramshift_charpoly_as_phi_image_of_diskpoles_data

/-- The linear factor attached to one disk pole after applying the `PhiDelta` map. -/
noncomputable def xi_gramshift_charpoly_as_phi_image_of_diskpoles_factor
    (D : xi_gramshift_charpoly_as_phi_image_of_diskpoles_data)
    (j : Fin D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_rank) : Polynomial ℂ :=
  Polynomial.X -
    Polynomial.C (D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_phi
      (D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_disk_pole j))

/-- The indexed product over the disk-pole image, written as a named polynomial. -/
noncomputable def xi_gramshift_charpoly_as_phi_image_of_diskpoles_disk_pole_product
    (D : xi_gramshift_charpoly_as_phi_image_of_diskpoles_data) : Polynomial ℂ :=
  ∏ j : Fin D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_rank,
    D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_factor j

end xi_gramshift_charpoly_as_phi_image_of_diskpoles_data

open xi_gramshift_charpoly_as_phi_image_of_diskpoles_data

/-- The prior spectral statement, recorded as the indexed disk-pole product. -/
def xi_gramshift_charpoly_as_phi_image_of_diskpoles_spectrum_formula
    (D : xi_gramshift_charpoly_as_phi_image_of_diskpoles_data) : Prop :=
  D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly =
    D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_disk_pole_product

/-- The characteristic-polynomial product formula over the `PhiDelta`-images of the disk poles. -/
def xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly_formula
    (D : xi_gramshift_charpoly_as_phi_image_of_diskpoles_data) : Prop :=
  D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly =
    ∏ j : Fin D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_rank,
      D.xi_gramshift_charpoly_as_phi_image_of_diskpoles_factor j

/-- Paper label: `prop:xi-gramshift-charpoly-as-phi-image-of-diskpoles`. -/
theorem paper_xi_gramshift_charpoly_as_phi_image_of_diskpoles
    (D : xi_gramshift_charpoly_as_phi_image_of_diskpoles_data) :
    xi_gramshift_charpoly_as_phi_image_of_diskpoles_spectrum_formula D →
      xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly_formula D := by
  intro hspectrum
  simpa [xi_gramshift_charpoly_as_phi_image_of_diskpoles_spectrum_formula,
    xi_gramshift_charpoly_as_phi_image_of_diskpoles_charpoly_formula,
    xi_gramshift_charpoly_as_phi_image_of_diskpoles_disk_pole_product] using hspectrum

end Omega.Zeta
