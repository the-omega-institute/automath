import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

/-- The one-coordinate Fourier phase contributed by a signed residue choice. -/
noncomputable def residueProfilePhaseFactor (x θ : ℝ) (b : Bool) : ℂ :=
  if b then Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)
  else Complex.exp (((-(x * θ) : ℝ) : ℂ) * Complex.I)

/-- The unnormalized Fourier transform obtained by summing over all bit-valued residue profiles. -/
noncomputable def residueProfileFourier {n : ℕ} (w : Fin n → ℝ) (θ : ℝ) : ℂ :=
  ∑ ε ∈ Fintype.piFinset (fun _ : Fin n => ({false, true} : Finset Bool)),
    ∏ i, residueProfilePhaseFactor (w i) θ (ε i)

/-- The normalized Fourier transform, i.e. the mean over all `2^n` residue profiles. -/
noncomputable def normalizedResidueProfileFourier {n : ℕ} (w : Fin n → ℝ) (θ : ℝ) : ℂ :=
  (((2 : ℂ) ^ n)⁻¹) * residueProfileFourier w θ

/-- The cosine factor contributed by one coordinate after averaging over the sign choice. -/
noncomputable def residueProfileCosFactor (x θ : ℝ) : ℂ :=
  (Real.cos (x * θ) : ℂ)

private theorem residueProfilePhaseFactor_sum (x θ : ℝ) :
    ∑ b ∈ ({false, true} : Finset Bool), residueProfilePhaseFactor x θ b =
      2 * residueProfileCosFactor x θ := by
  have htrue :
      residueProfilePhaseFactor x θ true =
        (Real.cos (x * θ) : ℂ) + (Real.sin (x * θ) : ℂ) * Complex.I := by
    simp [residueProfilePhaseFactor, Complex.exp_mul_I]
  have hfalse :
      residueProfilePhaseFactor x θ false =
        (Real.cos (x * θ) : ℂ) - (Real.sin (x * θ) : ℂ) * Complex.I := by
    simp [residueProfilePhaseFactor]
    rw [show -(↑x * ↑θ * Complex.I) = (((-(x * θ) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_mul_I]
    simpa [sub_eq_add_neg]
  rw [show ∑ b ∈ ({false, true} : Finset Bool), residueProfilePhaseFactor x θ b =
      residueProfilePhaseFactor x θ false + residueProfilePhaseFactor x θ true by simp]
  rw [hfalse, htrue]
  simp [residueProfileCosFactor]
  ring

/-- Paper-facing fold-spectrum factorization package: the Fourier sum over all residue profiles
factors coordinatewise, the normalized measure is the product of cosine factors, and its modulus is
the product of the corresponding absolute cosines.
    thm:fold-spectrum-factorization -/
theorem paper_fold_spectrum_factorization {n : ℕ} (w : Fin n → ℝ) (θ : ℝ) :
    residueProfileFourier w θ =
      ∏ i, ∑ b ∈ ({false, true} : Finset Bool), residueProfilePhaseFactor (w i) θ b ∧
    normalizedResidueProfileFourier w θ = ∏ i, residueProfileCosFactor (w i) θ ∧
    ‖normalizedResidueProfileFourier w θ‖ = ∏ i, |Real.cos (w i * θ)| := by
  have hprod :
      residueProfileFourier w θ =
        ∏ i, ∑ b ∈ ({false, true} : Finset Bool), residueProfilePhaseFactor (w i) θ b := by
    simpa [residueProfileFourier] using
      (Finset.sum_prod_piFinset (s := ({false, true} : Finset Bool))
        (g := fun i b => residueProfilePhaseFactor (w i) θ b))
  have hcos :
      residueProfileFourier w θ = ∏ i, 2 * residueProfileCosFactor (w i) θ := by
    rw [hprod]
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact residueProfilePhaseFactor_sum (w i) θ
  have hnormalized :
      normalizedResidueProfileFourier w θ = ∏ i, residueProfileCosFactor (w i) θ := by
    unfold normalizedResidueProfileFourier
    rw [hcos, Finset.prod_mul_distrib]
    rw [show ∏ i : Fin n, (2 : ℂ) = (2 : ℂ) ^ n by simp]
    have htwo : (2 : ℂ) ^ n ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    rw [← mul_assoc, inv_mul_cancel₀ htwo, one_mul]
  have hnorm :
      ‖normalizedResidueProfileFourier w θ‖ = ∏ i, |Real.cos (w i * θ)| := by
    rw [hnormalized]
    calc
      ‖∏ i, residueProfileCosFactor (w i) θ‖ = ∏ i, ‖residueProfileCosFactor (w i) θ‖ := by
        simpa using (norm_prod (s := Finset.univ) (f := fun i : Fin n => residueProfileCosFactor (w i) θ))
      _ = ∏ i, |Real.cos (w i * θ)| := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simpa [residueProfileCosFactor, Complex.ofReal_cos] using
          (Complex.norm_real (Real.cos (w i * θ)))
  exact ⟨hprod, hnormalized, hnorm⟩

end Omega.Folding
