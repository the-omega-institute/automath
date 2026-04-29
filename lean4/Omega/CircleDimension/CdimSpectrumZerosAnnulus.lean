import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Omega.Zeta.XiCdimSpectrumCompleteness

namespace Omega.CircleDimension

/-- The coefficient list of the circle-dimension spectrum partition polynomial. -/
def xi_cdim_spectrum_zeros_annulus_coefficients (factors : List ℕ) : List ℕ :=
  (List.range (factors.length + 1)).map (Omega.Zeta.xiCdimLambda factors)

/-- The successive coefficient ratio `a_k / a_{k+1}` of the partition polynomial. -/
def xi_cdim_spectrum_zeros_annulus_successive_ratio (factors : List ℕ) (k : ℕ) : ℕ :=
  Omega.Zeta.xiCdimLambda factors k / Omega.Zeta.xiCdimLambda factors (k + 1)

/-- The inner radius read from the last successive coefficient ratio. -/
def xi_cdim_spectrum_zeros_annulus_inner_radius (factors : List ℕ) : ℕ :=
  xi_cdim_spectrum_zeros_annulus_successive_ratio factors (factors.length - 1)

/-- The outer radius read from the first successive coefficient ratio. -/
def xi_cdim_spectrum_zeros_annulus_outer_radius (factors : List ℕ) : ℕ :=
  xi_cdim_spectrum_zeros_annulus_successive_ratio factors 0

/-- Paper label: `thm:xi-cdim-spectrum-zeros-annulus`.
The closed-form ratio formula for the circle-dimension partition polynomial identifies the annulus
data furnished by the positive-coefficient root bound: the first successive ratio is the outer
radius `n_t`, the last successive ratio is the inner radius `n₁`, and every intermediate ratio is
the corresponding invariant factor read in reverse order. -/
theorem paper_xi_cdim_spectrum_zeros_annulus (factors : List ℕ)
    (hfac : ∀ n ∈ factors, 1 < n) (hneq : factors ≠ []) :
    (∀ k : ℕ, k + 1 < factors.length →
      xi_cdim_spectrum_zeros_annulus_successive_ratio factors k =
        factors.get! (factors.length - 1 - k)) ∧
      xi_cdim_spectrum_zeros_annulus_inner_radius factors = factors[0]! ∧
      xi_cdim_spectrum_zeros_annulus_outer_radius factors = factors.get! (factors.length - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simpa [xi_cdim_spectrum_zeros_annulus_successive_ratio] using
      Omega.Zeta.paper_xi_cdim_spectrum_completeness factors hfac k hk
  · have hlen_pos : 0 < factors.length := List.length_pos_iff.mpr hneq
    cases factors with
    | nil =>
        contradiction
    | cons a as =>
        simp [xi_cdim_spectrum_zeros_annulus_inner_radius,
          xi_cdim_spectrum_zeros_annulus_successive_ratio, Omega.Zeta.xiCdimLambda]
  · cases factors with
    | nil =>
        contradiction
    | cons a as =>
        cases as with
        | nil =>
            calc
              xi_cdim_spectrum_zeros_annulus_outer_radius [a] = a := by
                simp [xi_cdim_spectrum_zeros_annulus_outer_radius,
                  xi_cdim_spectrum_zeros_annulus_successive_ratio, Omega.Zeta.xiCdimLambda]
              _ = [a].get! ([a].length - 1) := by
                change a = [a][0]!
                rfl
        | cons b bs =>
            have hratio :
                xi_cdim_spectrum_zeros_annulus_outer_radius (a :: b :: bs) =
                  (a :: b :: bs).get! ((a :: b :: bs).length - 1) := by
              simpa [xi_cdim_spectrum_zeros_annulus_outer_radius,
                xi_cdim_spectrum_zeros_annulus_successive_ratio] using
                Omega.Zeta.paper_xi_cdim_spectrum_completeness (a :: b :: bs)
                  (by simpa using hfac) 0 (by simp)
            simpa using hratio

end Omega.CircleDimension
