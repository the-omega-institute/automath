import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete prefixed finite-support data for the foldbin multiplicity Mellin rigidity theorem.
The support is stored as a strictly increasing `Fin n` prefix, and the two histograms are sampled
against the same support on the positive Mellin side and on the genus side. -/
structure conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data where
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize : ℕ
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support :
    Fin conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℕ
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity :
    Fin conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℕ
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity :
    Fin conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℕ
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_pos :
    ∀ i, 0 <
      conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_strict :
    StrictMono conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positive_moment_agreement :
    ∀ q : Fin conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      (∑ i,
          (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
            ℚ) *
            (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
              (q : ℕ)) =
        ∑ i,
          (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i :
            ℚ) *
            (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
              (q : ℕ)
  conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_sample_agreement :
    ∀ q : Fin conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      (∑ i,
          (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
            ℚ) *
            (1 /
              (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
                (2 : ℕ)) ^ (q : ℕ)) =
        ∑ i,
          (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i :
            ℚ) *
            (1 /
              (conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
                (2 : ℕ)) ^ (q : ℕ)

namespace conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data

def conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data)
    (hist :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℕ)
    (q : ℕ) : ℚ :=
  ∑ i, (hist i : ℚ) *
    (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^ q

def conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data)
    (hist :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℕ)
    (q : ℕ) : ℚ :=
  ∑ i, (hist i : ℚ) *
    (1 / (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
      (2 : ℕ)) ^ q

def statement
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) : Prop :=
  (∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity q =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity q) ∧
    (∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity q =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity q) ∧
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity

end conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data

private lemma conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_injective
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) :
    Function.Injective fun i =>
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) := by
  intro i j hij
  have hnat :
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j := by
    have hcast :
        (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) =
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j := by
      simpa using hij
    exact_mod_cast hcast
  exact
    D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_strict.injective hnat

private lemma conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_atom_injective
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) :
    Function.Injective fun i =>
      1 / (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
        (2 : ℕ) := by
  intro i j hij
  apply
    D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_strict.injective
  have hsq_inv :
      ((D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
          (2 : ℕ))⁻¹ =
        ((D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j : ℚ) ^
          (2 : ℕ))⁻¹ := by
    simpa [one_div] using hij
  have hsq :
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
          (2 : ℕ) =
        (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j : ℚ) ^
          (2 : ℕ) := by
    exact inv_inj.mp hsq_inv
  have hi_nonneg :
      0 ≤ (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) := by
    exact_mod_cast
      Nat.zero_le
        (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i)
  have hj_nonneg :
      0 ≤ (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j : ℚ) := by
    exact_mod_cast
      Nat.zero_le
        (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support j)
  exact_mod_cast (sq_eq_sq₀ hi_nonneg hj_nonneg).mp hsq

private lemma conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positive_eq
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) :
    D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity =
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity := by
  let f :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℚ :=
    fun i =>
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ)
  let v :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℚ :=
    fun i =>
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
          ℚ) -
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i
  have hf : Function.Injective f := by
    simpa [f] using
      conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support_injective D
  have hv :
      ∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
        (∑ i, v i * f i ^ (q : ℕ)) = 0 := by
    intro q
    have hsub :
        (∑ i,
            (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
              ℚ) *
              f i ^ (q : ℕ)) -
          (∑ i,
            (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i :
              ℚ) *
              f i ^ (q : ℕ)) = 0 := by
      exact sub_eq_zero.mpr
        (by
          simpa [f] using
            D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positive_moment_agreement
              q)
    simpa [v, sub_mul, Finset.sum_sub_distrib] using hsub
  have hv_zero : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hv
  funext i
  have hq :
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
          ℚ) -
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i =
          0 := by
    simpa [v] using congr_fun hv_zero i
  exact_mod_cast sub_eq_zero.mp hq

private lemma conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_eq
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) :
    D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity =
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity := by
  let f :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℚ :=
    fun i =>
      1 / (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_support i : ℚ) ^
        (2 : ℕ)
  let v :
      Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize → ℚ :=
    fun i =>
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
          ℚ) -
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i
  have hf : Function.Injective f := by
    simpa [f] using
      conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_atom_injective D
  have hv :
      ∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
        (∑ i, v i * f i ^ (q : ℕ)) = 0 := by
    intro q
    have hsub :
        (∑ i,
            (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
              ℚ) *
              f i ^ (q : ℕ)) -
          (∑ i,
            (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i :
              ℚ) *
              f i ^ (q : ℕ)) = 0 := by
      exact sub_eq_zero.mpr
        (by
          simpa [f] using
            D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_sample_agreement
              q)
    simpa [v, sub_mul, Finset.sum_sub_distrib] using hsub
  have hv_zero : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hv
  funext i
  have hq :
      (D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity i :
          ℚ) -
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity i =
          0 := by
    simpa [v] using congr_fun hv_zero i
  exact_mod_cast sub_eq_zero.mp hq

/-- Paper label: `thm:conclusion-foldbin-multiplicity-mellin-finite-support-rigidity`. -/
theorem paper_conclusion_foldbin_multiplicity_mellin_finite_support_rigidity
    (D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simpa [
      conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment] using
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positive_moment_agreement q
  · intro q
    simpa [
      conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample,
      one_div, inv_pow] using
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_sample_agreement q
  · exact conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genus_eq D

end Omega.Conclusion
