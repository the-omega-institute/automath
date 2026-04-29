import Omega.Zeta.BlaschkePointSpectrumCorrespondence

namespace Omega.Zeta

/-- Concrete finite-defect data for
`cor:xi-cmv-point-spectrum-dimension-equals-blaschke-degree`.  The record names the CMV
point-spectrum dimension and the finite Blaschke degree, both tied to the existing
Blaschke/model-space correspondence package. -/
structure xi_cmv_point_spectrum_dimension_equals_blaschke_degree_data where
  xi_cmv_point_spectrum_dimension_equals_blaschke_degree_correspondence :
    blaschke_point_spectrum_correspondence_data
  xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree : ℕ
  xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension : ℕ
  xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree_eq :
    xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree =
      xi_cmv_point_spectrum_dimension_equals_blaschke_degree_correspondence.blaschkeDegree
  xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension_eq :
    xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension =
      xi_cmv_point_spectrum_dimension_equals_blaschke_degree_correspondence.pointSpectrumDimension

/-- In the finite-dimensional CMV residual sector, no point spectrum means zero residual
point-spectrum dimension. -/
def xi_cmv_point_spectrum_dimension_equals_blaschke_degree_no_point_spectrum
    (D : xi_cmv_point_spectrum_dimension_equals_blaschke_degree_data) : Prop :=
  D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension = 0

/-- Concrete statement of the corollary: the finite CMV point-spectrum dimension equals the
finite Blaschke degree, and zero Blaschke degree is equivalent to no finite point spectrum. -/
def xi_cmv_point_spectrum_dimension_equals_blaschke_degree_statement
    (D : xi_cmv_point_spectrum_dimension_equals_blaschke_degree_data) : Prop :=
  D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension =
      D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree ∧
    (D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree = 0 ↔
      xi_cmv_point_spectrum_dimension_equals_blaschke_degree_no_point_spectrum D)

/-- Paper label: `cor:xi-cmv-point-spectrum-dimension-equals-blaschke-degree`. -/
theorem paper_xi_cmv_point_spectrum_dimension_equals_blaschke_degree
    (D : xi_cmv_point_spectrum_dimension_equals_blaschke_degree_data) :
    xi_cmv_point_spectrum_dimension_equals_blaschke_degree_statement D := by
  let C := D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_correspondence
  have hcorr := (paper_blaschke_point_spectrum_correspondence C).2
  have hdim_degree :
      D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension =
        D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree := by
    calc
      D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension =
          C.pointSpectrumDimension :=
        D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_point_spectrum_dimension_eq
      _ = C.blaschkeDegree := hcorr
      _ =
          D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree :=
        D.xi_cmv_point_spectrum_dimension_equals_blaschke_degree_finite_blaschke_degree_eq.symm
  refine ⟨hdim_degree, ?_⟩
  constructor
  · intro hdegree
    dsimp [xi_cmv_point_spectrum_dimension_equals_blaschke_degree_no_point_spectrum]
    exact hdim_degree.trans hdegree
  · intro hno
    dsimp [xi_cmv_point_spectrum_dimension_equals_blaschke_degree_no_point_spectrum] at hno
    exact hdim_degree.symm.trans hno

end Omega.Zeta
