import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.EllipsoidIsoperimetricVariance
import Omega.SPG.EllipsoidBoundaryFluxReconstruction

namespace Omega.POM

open scoped BigOperators

/-- Concrete data for reconstructing the logarithmic ellipsoid variance from the zeroth and first
boundary fluxes. The field `eigvals` records the reconstructed eigenvalues, while `hvolume` and
`heigvals` encode the `B₀`-volume and spectrum identities used in the paper reduction. -/
structure EllipsoidBoundaryCertificateData where
  d : ℕ
  hd : 2 ≤ d
  volume : ℝ
  B0 : ℝ
  ell : Fin d → ℝ
  eigvals : Fin d → ℝ
  hvolume : volume = B0 / d
  heigvals : ∀ i : Fin d, eigvals i = (ell i) ^ 2
  hell : ∀ i : Fin d, 0 < ell i

namespace EllipsoidBoundaryCertificateData

/-- The spectrum decoded from the boundary matrix. -/
noncomputable def boundarySpectrum (D : EllipsoidBoundaryCertificateData) (i : Fin D.d) : ℝ :=
  D.eigvals i

/-- The semiaxis logarithmic variance, viewed as the paper's ellipsoid deficit certificate. -/
noncomputable def surfaceDeficit (D : EllipsoidBoundaryCertificateData) : ℝ :=
  ellipsoidLogVariance D.d D.ell

/-- The quarter-scaled logarithmic variance of the reconstructed eigenvalue spectrum. -/
noncomputable def boundaryVarianceLowerBound (D : EllipsoidBoundaryCertificateData) : ℝ :=
  (1 / 4 : ℝ) * ellipsoidLogVariance D.d D.boundarySpectrum

private lemma ellipsoidLogMean_sq (d : ℕ) (hd : 0 < d) (ell : Fin d → ℝ) (hell : ∀ i, 0 < ell i) :
    ellipsoidLogMean d (fun i => (ell i) ^ 2) = 2 * ellipsoidLogMean d ell := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hsum :
      (∑ i : Fin d, Real.log ((ell i) ^ 2)) = 2 * ∑ i : Fin d, Real.log (ell i) := by
    calc
      (∑ i : Fin d, Real.log ((ell i) ^ 2)) = ∑ i : Fin d, (2 * Real.log (ell i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hlog :
            Real.log ((ell i) ^ 2) = 2 * Real.log (ell i) := by
          rw [pow_two, Real.log_mul (ne_of_gt (hell i)) (ne_of_gt (hell i))]
          ring
        rw [hlog]
      _ = 2 * ∑ i : Fin d, Real.log (ell i) := by
        simpa using
          (Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ))
            (f := fun i => Real.log (ell i))).symm
  unfold ellipsoidLogMean
  rw [hsum]
  calc
    (2 * ∑ i : Fin d, Real.log (ell i)) / d = 2 * ((∑ i : Fin d, Real.log (ell i)) / d) := by
      field_simp [hd0]
    _ = 2 * ellipsoidLogMean d ell := by
      rfl

private lemma ellipsoidLogVariance_sq (d : ℕ) (hd : 0 < d) (ell : Fin d → ℝ)
    (hell : ∀ i, 0 < ell i) :
    ellipsoidLogVariance d (fun i => (ell i) ^ 2) = 4 * ellipsoidLogVariance d ell := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hmean : ellipsoidLogMean d (fun i => (ell i) ^ 2) = 2 * ellipsoidLogMean d ell :=
    ellipsoidLogMean_sq d hd ell hell
  unfold ellipsoidLogVariance
  rw [hmean]
  have hsum :
      (∑ i : Fin d, (Real.log ((ell i) ^ 2) - 2 * ellipsoidLogMean d ell) ^ 2) =
        4 * ∑ i : Fin d, (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2 := by
    calc
      (∑ i : Fin d, (Real.log ((ell i) ^ 2) - 2 * ellipsoidLogMean d ell) ^ 2) =
          ∑ i : Fin d, (4 * (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlog :
                Real.log ((ell i) ^ 2) = 2 * Real.log (ell i) := by
              rw [pow_two, Real.log_mul (ne_of_gt (hell i)) (ne_of_gt (hell i))]
              ring
            rw [hlog]
            ring
      _ = 4 * ∑ i : Fin d, (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2 := by
            simpa using
              (Finset.mul_sum (s := Finset.univ) (a := (4 : ℝ))
                (f := fun i => (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2)).symm
  rw [hsum]
  calc
    (4 * ∑ i : Fin d, (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2) / d =
        4 * ((∑ i : Fin d, (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2) / d) := by
          field_simp [hd0]
    _ = 4 * ellipsoidLogVariance d ell := by
      rfl

lemma boundarySpectrum_eq_axisSq (D : EllipsoidBoundaryCertificateData) (i : Fin D.d) :
    D.boundarySpectrum i = (D.ell i) ^ 2 := by
  exact D.heigvals i

end EllipsoidBoundaryCertificateData

open EllipsoidBoundaryCertificateData

/-- Paper label: `cor:pom-ellipsoid-isoperimetric-boundary-certificate`.
The semiaxis log-variance equals one quarter of the reconstructed log-spectrum variance. -/
theorem paper_pom_ellipsoid_isoperimetric_boundary_certificate
    (D : EllipsoidBoundaryCertificateData) :
    D.surfaceDeficit >= D.boundaryVarianceLowerBound := by
  have hd_pos : 0 < D.d := lt_of_lt_of_le (by decide : 0 < 2) D.hd
  have hspectrum :
      ellipsoidLogVariance D.d (fun i => (D.ell i) ^ 2) = ellipsoidLogVariance D.d D.boundarySpectrum := by
    refine congrArg (ellipsoidLogVariance D.d) ?_
    funext i
    exact (D.boundarySpectrum_eq_axisSq i).symm
  have heq : D.surfaceDeficit = D.boundaryVarianceLowerBound := by
    unfold EllipsoidBoundaryCertificateData.surfaceDeficit
      EllipsoidBoundaryCertificateData.boundaryVarianceLowerBound
    rw [← hspectrum, ellipsoidLogVariance_sq D.d hd_pos D.ell D.hell]
    ring
  exact heq.ge

end Omega.POM
