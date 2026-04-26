import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyLeyangUniversalKernels

namespace Omega.Folding

/-- The odd-kernel zero lattice `w = i π k`. -/
noncomputable def foldGaugeAnomalyLeyangOddZeroParameter (k : ℕ) : ℂ :=
  ((k : ℂ) * (Real.pi : ℂ)) * Complex.I

/-- The even-kernel zero lattice `w = i π (k + 1/2)`. -/
noncomputable def foldGaugeAnomalyLeyangEvenZeroParameter (k : ℕ) : ℂ :=
  (((k : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) * Complex.I

/-- The deleted-branch quadratic lattice point in the odd `sinh(w)/w` regime. -/
noncomputable def foldGaugeAnomalyLeyangOddQuadraticZero (uStar bStar : ℂ) (m k : ℕ) : ℂ :=
  foldGaugeAnomalyLeyangScaledPoint uStar bStar (foldGaugeAnomalyLeyangOddZeroParameter k) m

/-- The deleted-branch quadratic lattice point in the even `cosh(w)` regime. -/
noncomputable def foldGaugeAnomalyLeyangEvenQuadraticZero (uStar bStar : ℂ) (m k : ℕ) : ℂ :=
  foldGaugeAnomalyLeyangScaledPoint uStar bStar (foldGaugeAnomalyLeyangEvenZeroParameter k) m

/-- The branch-point direction invariant extracted from the `m^{-2}` rescaling. -/
noncomputable def foldGaugeAnomalyLeyangDirectionInvariant (bStar : ℂ) : ℂ :=
  -1 / bStar

private lemma foldGaugeAnomalyLeyangOddZero_square (k : ℕ) :
    foldGaugeAnomalyLeyangOddZeroParameter k ^ 2 =
      -((Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2) := by
  unfold foldGaugeAnomalyLeyangOddZeroParameter
  ring_nf
  simp [Complex.I_sq]

private lemma foldGaugeAnomalyLeyangEvenZero_square (k : ℕ) :
    foldGaugeAnomalyLeyangEvenZeroParameter k ^ 2 =
      -((Real.pi : ℂ) ^ 2 * ((k : ℂ) + 1 / 2) ^ 2) := by
  unfold foldGaugeAnomalyLeyangEvenZeroParameter
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The universal Lee--Yang kernels place their zeros on quadratic lattices after the
`u = u_* + w^2 / (b_* m^2)` rescaling, and the common approach direction is `-1 / b_*`.
    cor:fold-gauge-anomaly-leyang-quadratic-lattice-zeros -/
theorem paper_fold_gauge_anomaly_leyang_quadratic_lattice_zeros
    (uStar bStar μStar C1 C0 : ℂ) (hb : bStar ≠ 0) (hμ : μStar ≠ 0) :
    (∀ m : ℕ, 1 ≤ m →
      ∀ k : ℕ,
        foldGaugeAnomalyLeyangOddQuadraticZero uStar bStar m k =
          uStar - ((Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2) / (bStar * (m : ℂ) ^ 2)) ∧
    (∀ m : ℕ, 1 ≤ m →
      ∀ k : ℕ,
        foldGaugeAnomalyLeyangEvenQuadraticZero uStar bStar m k =
          uStar - ((Real.pi : ℂ) ^ 2 * ((k : ℂ) + 1 / 2) ^ 2) / (bStar * (m : ℂ) ^ 2)) ∧
    foldGaugeAnomalyLeyangDirectionInvariant bStar = -1 / bStar := by
  let _ := paper_fold_gauge_anomaly_leyang_universal_kernels uStar bStar μStar C1 C0 0 hb hμ
  refine ⟨?_, ?_, rfl⟩
  · intro m hm k
    have hm0 : (m : ℂ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    unfold foldGaugeAnomalyLeyangOddQuadraticZero foldGaugeAnomalyLeyangScaledPoint
    rw [foldGaugeAnomalyLeyangOddZero_square]
    field_simp [hb, hm0]
    ring
  · intro m hm k
    have hm0 : (m : ℂ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    unfold foldGaugeAnomalyLeyangEvenQuadraticZero foldGaugeAnomalyLeyangScaledPoint
    rw [foldGaugeAnomalyLeyangEvenZero_square]
    field_simp [hb, hm0]
    ring

end Omega.Folding
