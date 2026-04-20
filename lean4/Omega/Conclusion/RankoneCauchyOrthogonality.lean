import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The coordinatewise candidate eigenvector for the diagonal-plus-rank-one update
`A(b) = D₀ + b g gᵀ`. -/
noncomputable def rankoneCandidateEigenvector {n : Nat}
    (D0 g : Fin n → ℝ) (lam : ℝ) : Fin n → ℝ :=
  fun i => g i / (lam - D0 i)

/-- The Cauchy secant equation attached to the rank-one update. -/
noncomputable def rankoneCauchySecant {n : Nat}
    (D0 g : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, (g i) ^ 2 / (lam - D0 i)

/-- The cross term appearing in the orthogonality relation for two distinct eigenvalues. -/
noncomputable def rankoneCauchyCrossTerm {n : Nat}
    (D0 g : Fin n → ℝ) (lam mu : ℝ) : ℝ :=
  ∑ i, (g i) ^ 2 / ((lam - D0 i) * (mu - D0 i))

private theorem rankone_cauchy_difference {n : Nat} (D0 g : Fin n → ℝ) {lam mu : ℝ}
    (hlamdiag : ∀ i, lam ≠ D0 i) (hmudiag : ∀ i, mu ≠ D0 i) :
    rankoneCauchySecant D0 g lam - rankoneCauchySecant D0 g mu =
      (mu - lam) * rankoneCauchyCrossTerm D0 g lam mu := by
  unfold rankoneCauchySecant rankoneCauchyCrossTerm
  calc
    (∑ i, (g i) ^ 2 / (lam - D0 i)) - ∑ i, (g i) ^ 2 / (mu - D0 i) =
        ∑ i, ((g i) ^ 2 / (lam - D0 i) - (g i) ^ 2 / (mu - D0 i)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, (mu - lam) * ((g i) ^ 2 / ((lam - D0 i) * (mu - D0 i))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hlam' : lam - D0 i ≠ 0 := sub_ne_zero.mpr (hlamdiag i)
          have hmu' : mu - D0 i ≠ 0 := sub_ne_zero.mpr (hmudiag i)
          field_simp [hlam', hmu']
          ring
    _ = (mu - lam) * ∑ i, (g i) ^ 2 / ((lam - D0 i) * (mu - D0 i)) := by
          rw [Finset.mul_sum]
    _ = (mu - lam) * rankoneCauchyCrossTerm D0 g lam mu := by rfl

/-- For the symmetric rank-one update `A(b) = D₀ + b g gᵀ`, the candidate eigenvector
`(λ I - D₀)⁻¹ g` satisfies the coordinatewise eigenvalue equation, the secant equations take the
common value `1 / b`, and orthogonality of distinct eigenvectors forces the Cauchy cross term to
vanish.
    prop:conclusion-rankone-cauchy-orthogonality -/
theorem paper_conclusion_rankone_cauchy_orthogonality {n : Nat}
    (D0 g : Fin n → ℝ) {b lam mu : ℝ}
    (hlamdiag : ∀ i, lam ≠ D0 i) (hmudiag : ∀ i, mu ≠ D0 i) (hlammu : lam ≠ mu)
    (hlam : rankoneCauchySecant D0 g lam = 1 / b)
    (hmu : rankoneCauchySecant D0 g mu = 1 / b) :
    (∀ i, (lam - D0 i) * rankoneCandidateEigenvector D0 g lam i = g i) ∧
      (∀ i, (mu - D0 i) * rankoneCandidateEigenvector D0 g mu i = g i) ∧
      rankoneCauchyCrossTerm D0 g lam mu = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold rankoneCandidateEigenvector
    have hlam' : lam - D0 i ≠ 0 := sub_ne_zero.mpr (hlamdiag i)
    field_simp [hlam']
  · intro i
    unfold rankoneCandidateEigenvector
    have hmu' : mu - D0 i ≠ 0 := sub_ne_zero.mpr (hmudiag i)
    field_simp [hmu']
  · have hDiff :=
      rankone_cauchy_difference D0 g hlamdiag hmudiag
    have hZero :
        (mu - lam) * rankoneCauchyCrossTerm D0 g lam mu = 0 := by
      calc
        (mu - lam) * rankoneCauchyCrossTerm D0 g lam mu =
            rankoneCauchySecant D0 g lam - rankoneCauchySecant D0 g mu := by
              symm
              exact hDiff
        _ = 1 / b - 1 / b := by rw [hlam, hmu]
        _ = 0 := by ring
    have hFactor : mu - lam ≠ 0 := sub_ne_zero.mpr hlammu.symm
    rcases mul_eq_zero.mp hZero with hMul | hMul
    · exact False.elim (hFactor hMul)
    · exact hMul

end Omega.Conclusion
