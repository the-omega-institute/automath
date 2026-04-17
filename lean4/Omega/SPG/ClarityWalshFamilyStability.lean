import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Core finite-family estimate behind the Walsh-family stability corollary:
    a uniform pointwise bound on Walsh coefficients controls the sum of their squared
    magnitudes by `|I| * eps^2`.
    cor:spg-clarity-walsh-family-stability -/
theorem paper_spg_clarity_walsh_family_stability {ι : Type} [DecidableEq ι]
    (I : Finset ι) (a : ι → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (ha : ∀ i ∈ I, |a i| ≤ eps) :
    Finset.sum I (fun i => |a i| ^ 2) ≤ I.card * eps ^ 2 := by
  have hsq : ∀ i ∈ I, |a i| ^ 2 ≤ eps ^ 2 := by
    intro i hi
    nlinarith [ha i hi, abs_nonneg (a i), heps]
  calc
    Finset.sum I (fun i => |a i| ^ 2) ≤ Finset.sum I (fun _ => eps ^ 2) := by
      exact Finset.sum_le_sum (fun i hi => hsq i hi)
    _ = I.card * eps ^ 2 := by
      simp [nsmul_eq_mul]

/-- Singleton-index specialization of the Walsh-family stability estimate.
    cor:spg-clarity-walsh-spectral-stability -/
theorem paper_spg_clarity_walsh_spectral_stability {ι : Type} [DecidableEq ι]
    (i : ι) (a : ι → ℝ) (eps : ℝ) (heps : 0 ≤ eps) (ha : |a i| ≤ eps) :
    Finset.sum ({i} : Finset ι) (fun j => |a j| ^ 2) ≤ eps ^ 2 := by
  simpa using
    paper_spg_clarity_walsh_family_stability ({i} : Finset ι) a eps heps
      (by
        intro j hj
        have hji : j = i := by simpa using hj
        simpa [hji] using ha)

end Omega.SPG
