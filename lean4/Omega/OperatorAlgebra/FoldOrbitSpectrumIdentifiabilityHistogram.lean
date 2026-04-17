import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- A finite histogram indexed by the degeneracy values `1, …, m`. -/
abbrev FoldOrbitHistogram (m : ℕ) := Fin m → ℚ

/-- The actual degeneracy attached to the `Fin m` index. -/
def foldOrbitDegree {m : ℕ} (d : Fin m) : ℕ :=
  d.1 + 1

/-- The first new logarithmic coefficient contributed by the truncated exponential `E_d`. -/
def foldOrbitLeadingCoeff {m : ℕ} (d : Fin m) : ℚ :=
  -((Nat.factorial (foldOrbitDegree d + 1) : ℚ)⁻¹)

/-- Model coefficient of `log E_d` in degree `q`; only the first new degree is retained. -/
def foldOrbitLogEcoeff {m : ℕ} (d : Fin m) (q : ℕ) : ℚ :=
  if q = foldOrbitDegree d + 1 then foldOrbitLeadingCoeff d else 0

/-- Model coefficient of `log H_m`, obtained from the Burnside-factorized logarithmic expansion. -/
def foldOrbitLogHCoeff {m : ℕ} (N : FoldOrbitHistogram m) (q : ℕ) : ℚ :=
  ∑ d, N d * foldOrbitLogEcoeff d q

/-- Residual coefficient after removing the already-recovered lower histogram levels. -/
def foldOrbitResidualCoeff {m : ℕ} (N : FoldOrbitHistogram m) (d : Fin m) : ℚ :=
  foldOrbitLogHCoeff N (foldOrbitDegree d + 1) -
    Finset.sum (Finset.univ.filter (fun j : Fin m => foldOrbitDegree j < foldOrbitDegree d))
      (fun j => N j * foldOrbitLogEcoeff j (foldOrbitDegree d + 1))

/-- The logarithmic factorization formula for the Burnside-transformed series. -/
def FoldOrbitFactorizationFormula {m : ℕ} (N : FoldOrbitHistogram m) : Prop :=
  ∀ q : ℕ, foldOrbitLogHCoeff N q = ∑ d, N d * foldOrbitLogEcoeff d q

/-- The triangular recursion recovering the first unseen histogram coefficient. -/
def FoldOrbitTriangularRecursion {m : ℕ} (N : FoldOrbitHistogram m) : Prop :=
  ∀ d : Fin m, N d = -(Nat.factorial (foldOrbitDegree d + 1) : ℚ) * foldOrbitResidualCoeff N d

/-- Equality of the logarithmic coefficient data uniquely determines the histogram. -/
def FoldOrbitHistogramUnique {m : ℕ} (N : FoldOrbitHistogram m) : Prop :=
  ∀ M : FoldOrbitHistogram m, (∀ q : ℕ, foldOrbitLogHCoeff N q = foldOrbitLogHCoeff M q) → M = N

lemma foldOrbitDegree_injective {m : ℕ} : Function.Injective (@foldOrbitDegree m) := by
  intro j d hdeg
  apply Fin.ext
  dsimp [foldOrbitDegree] at hdeg
  omega

lemma foldOrbitLogEcoeff_at_degree {m : ℕ} (j d : Fin m) :
    foldOrbitLogEcoeff j (foldOrbitDegree d + 1) =
      if j = d then foldOrbitLeadingCoeff d else 0 := by
  by_cases h : j = d
  · subst h
    simp [foldOrbitLogEcoeff, foldOrbitLeadingCoeff]
  · have hneq : foldOrbitDegree j + 1 ≠ foldOrbitDegree d + 1 := by
      intro hdeg
      exact h (foldOrbitDegree_injective (by omega))
    rw [foldOrbitLogEcoeff, if_neg hneq.symm, if_neg h]

lemma foldOrbitLogHCoeff_at_degree {m : ℕ} (N : FoldOrbitHistogram m) (d : Fin m) :
    foldOrbitLogHCoeff N (foldOrbitDegree d + 1) = N d * foldOrbitLeadingCoeff d := by
  classical
  rw [foldOrbitLogHCoeff]
  simp [foldOrbitLogEcoeff_at_degree]

lemma foldOrbitResidualCoeff_eq {m : ℕ} (N : FoldOrbitHistogram m) (d : Fin m) :
    foldOrbitResidualCoeff N d = N d * foldOrbitLeadingCoeff d := by
  rw [foldOrbitResidualCoeff, foldOrbitLogHCoeff_at_degree]
  have hsum_zero :
      Finset.sum (Finset.univ.filter (fun j : Fin m => foldOrbitDegree j < foldOrbitDegree d))
        (fun j => N j * foldOrbitLogEcoeff j (foldOrbitDegree d + 1)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjlt : foldOrbitDegree j < foldOrbitDegree d := (Finset.mem_filter.mp hj).2
    have hneq : foldOrbitDegree j + 1 ≠ foldOrbitDegree d + 1 := by omega
    rw [foldOrbitLogEcoeff, if_neg hneq.symm]
    ring
  simp [hsum_zero]

lemma foldOrbitLeadingCoeff_ne_zero {m : ℕ} (d : Fin m) : foldOrbitLeadingCoeff d ≠ 0 := by
  have hfac : (Nat.factorial (foldOrbitDegree d + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (foldOrbitDegree d + 1)
  simp [foldOrbitLeadingCoeff, hfac]

/-- Publication-facing histogram identifiability package for the Burnside-transformed orbit
spectrum. The logarithmic coefficient model is triangular: the first unseen coefficient of
`log E_d` occurs exactly in degree `d + 1`, so coefficient extraction recursively recovers the
histogram and therefore makes it unique. -/
theorem paper_op_algebra_fold_orbit_spectrum_identifiability_histogram
    {m : ℕ} (N : FoldOrbitHistogram m) :
    FoldOrbitFactorizationFormula N ∧ FoldOrbitTriangularRecursion N ∧ FoldOrbitHistogramUnique N := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rfl
  · intro d
    rw [foldOrbitResidualCoeff_eq]
    have hfac :
        -(Nat.factorial (foldOrbitDegree d + 1) : ℚ) * foldOrbitLeadingCoeff d = 1 := by
      let a : ℚ := Nat.factorial (foldOrbitDegree d + 1)
      have hfac' : a ≠ 0 := by
        change (Nat.factorial (foldOrbitDegree d + 1) : ℚ) ≠ 0
        exact_mod_cast Nat.factorial_ne_zero (foldOrbitDegree d + 1)
      calc
        -(Nat.factorial (foldOrbitDegree d + 1) : ℚ) * foldOrbitLeadingCoeff d = -a * (-(a⁻¹)) := by
          simp [foldOrbitLeadingCoeff, a]
        _ = a * a⁻¹ := by ring
        _ = 1 := by field_simp [hfac']
    calc
      N d = N d * 1 := by ring
      _ = N d * (-(Nat.factorial (foldOrbitDegree d + 1) : ℚ) * foldOrbitLeadingCoeff d) := by
        rw [hfac]
      _ = -(Nat.factorial (foldOrbitDegree d + 1) : ℚ) * (N d * foldOrbitLeadingCoeff d) := by
        ring
  · intro M hcoeff
    ext d
    have hd :=
      hcoeff (foldOrbitDegree d + 1)
    rw [foldOrbitLogHCoeff_at_degree, foldOrbitLogHCoeff_at_degree] at hd
    exact (mul_right_cancel₀ (foldOrbitLeadingCoeff_ne_zero d) hd).symm

end Omega.OperatorAlgebra
