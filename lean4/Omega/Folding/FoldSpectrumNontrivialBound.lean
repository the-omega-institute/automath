import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.Folding.FoldSpectrumFactorization

open scoped BigOperators

namespace Omega.Folding

/-- A nontrivial cosine factor forces the unnormalized residue-profile Fourier norm below `2^n`.
    cor:fold-spectrum-nontrivial-bound -/
theorem paper_fold_spectrum_nontrivial_bound {n : ℕ} (w : Fin n → ℝ) (θ : ℝ)
    (hstrict : ∃ i : Fin n, |Real.cos (w i * θ)| < 1) :
    ‖Omega.Folding.residueProfileFourier w θ‖ < (2 : ℝ) ^ n := by
  rcases paper_fold_spectrum_factorization (w := w) (θ := θ) with ⟨_, _, hnorm⟩
  rcases hstrict with ⟨i, hi⟩
  let rest : ℝ := Finset.prod (Finset.univ \ {i}) (fun j : Fin n => |Real.cos (w j * θ)|)
  have hrest_nonneg : 0 ≤ rest := by
    refine Finset.prod_nonneg ?_
    intro j hj
    exact abs_nonneg _
  have hrest_le_one : rest ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro j hj
      exact abs_nonneg _
    · intro j hj
      exact Real.abs_cos_le_one (w j * θ)
  have hsplit :
      ∏ j : Fin n, |Real.cos (w j * θ)| =
        |Real.cos (w i * θ)| * rest := by
    simpa [rest] using
      (Finset.prod_eq_mul_prod_diff_singleton
        (s := Finset.univ) (i := i) (f := fun j : Fin n => |Real.cos (w j * θ)|) (by simp))
  have hprod_lt : ∏ j : Fin n, |Real.cos (w j * θ)| < 1 := by
    rw [hsplit]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) hi hrest_le_one
  have htwo_ne_zero : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  have hfourier :
      residueProfileFourier w θ = ((2 : ℂ) ^ n) * normalizedResidueProfileFourier w θ := by
    symm
    unfold normalizedResidueProfileFourier
    rw [← mul_assoc, mul_inv_cancel₀ htwo_ne_zero, one_mul]
  have hpow_norm : ‖((2 : ℂ) ^ n)‖ = (2 : ℝ) ^ n := by
    calc
      ‖((2 : ℂ) ^ n)‖ = ‖(((2 : ℝ) ^ n : ℂ))‖ := by simp
      _ = (2 : ℝ) ^ n := by simp
  have hnorm_fourier :
      ‖residueProfileFourier w θ‖ = (2 : ℝ) ^ n * ∏ i : Fin n, |Real.cos (w i * θ)| := by
    rw [hfourier, norm_mul, hpow_norm, hnorm]
  have hlt : ‖residueProfileFourier w θ‖ < (2 : ℝ) ^ n * 1 := by
    rw [hnorm_fourier]
    have htwo_pos : 0 < (2 : ℝ) ^ n := by positivity
    simpa using mul_lt_mul_of_pos_left hprod_lt htwo_pos
  simpa using hlt

end Omega.Folding
