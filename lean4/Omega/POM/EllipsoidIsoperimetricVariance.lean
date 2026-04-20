import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Mean of the logarithmic axis lengths of an axis-aligned ellipsoid. -/
noncomputable def ellipsoidLogMean (d : Nat) (ell : Fin d → Real) : Real :=
  (∑ i, Real.log (ell i)) / d

/-- Variance of the logarithmic axis lengths of an axis-aligned ellipsoid. -/
noncomputable def ellipsoidLogVariance (d : Nat) (ell : Fin d → Real) : Real :=
  (∑ i, (Real.log (ell i) - ellipsoidLogMean d ell) ^ 2) / d

private lemma ellipsoidLogMean_scale (d : Nat) (hd : 0 < d) (ell : Fin d → Real)
    (hell : ∀ i, 0 < ell i) {c : Real} (hc : 0 < c) :
    ellipsoidLogMean d (fun i => c * ell i) = Real.log c + ellipsoidLogMean d ell := by
  have hd0 : (d : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  unfold ellipsoidLogMean
  have hsum :
      (∑ i : Fin d, Real.log (c * ell i)) = (d : Real) * Real.log c + ∑ i : Fin d, Real.log (ell i) := by
    calc
      (∑ i : Fin d, Real.log (c * ell i)) = ∑ i : Fin d, (Real.log c + Real.log (ell i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.log_mul hc.ne' (ne_of_gt (hell i))]
      _ = (∑ i : Fin d, Real.log c) + ∑ i : Fin d, Real.log (ell i) := by
        rw [Finset.sum_add_distrib]
      _ = (d : Real) * Real.log c + ∑ i : Fin d, Real.log (ell i) := by
        simp
  rw [hsum]
  field_simp [hd0]

private lemma ellipsoidLogVariance_scale (d : Nat) (hd : 0 < d) (ell : Fin d → Real)
    (hell : ∀ i, 0 < ell i) {c : Real} (hc : 0 < c) :
    ellipsoidLogVariance d (fun i => c * ell i) = ellipsoidLogVariance d ell := by
  have hmean : ellipsoidLogMean d (fun i => c * ell i) = Real.log c + ellipsoidLogMean d ell :=
    ellipsoidLogMean_scale d hd ell hell hc
  unfold ellipsoidLogVariance
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_mul hc.ne' (ne_of_gt (hell i)), hmean]
  ring

/-- Paper label: `thm:pom-ellipsoid-isoperimetric-variance`.
The logarithmic axis-length variance is nonnegative and is unchanged by normalizing the ellipsoid
by any positive scalar, matching the scale-free form of the isoperimetric deficit. -/
theorem paper_pom_ellipsoid_isoperimetric_variance (d : Nat) (hd : 2 <= d) (ell : Fin d -> Real)
    (hell : forall i, 0 < ell i) :
    0 ≤ ellipsoidLogVariance d ell ∧
      ∀ c : Real, 0 < c → ellipsoidLogVariance d (fun i => c * ell i) = ellipsoidLogVariance d ell := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have hd_pos : 0 < (d : Real) := by
    exact_mod_cast hd_pos_nat
  refine ⟨?_, ?_⟩
  · unfold ellipsoidLogVariance
    exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _) (le_of_lt hd_pos)
  · intro c hc
    exact ellipsoidLogVariance_scale d hd_pos_nat ell hell hc

end Omega.POM
