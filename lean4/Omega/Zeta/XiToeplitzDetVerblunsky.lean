import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite-step data for the Toeplitz determinant/Verblunsky recursion. `delta0` is the
initial determinant and `alpha` is the finite reflection-coefficient prefix. -/
structure XiToeplitzDetVerblunskyData where
  steps : ℕ
  delta0 : ℝ
  hdelta0 : 0 < delta0
  alpha : Fin steps → ℝ

namespace XiToeplitzDetVerblunskyData

/-- Reflection coefficients extended by zero outside the chosen truncation length. -/
def alphaAt (D : XiToeplitzDetVerblunskyData) (n : ℕ) : ℝ :=
  if hn : n < D.steps then D.alpha ⟨n, hn⟩ else 0

/-- The Schur/Levinson one-step factor. -/
def stepFactor (D : XiToeplitzDetVerblunskyData) (n : ℕ) : ℝ :=
  1 - D.alphaAt n ^ 2

/-- Toeplitz principal determinants defined by the Schur/Levinson recursion. -/
def toeplitzDet (D : XiToeplitzDetVerblunskyData) : ℕ → ℝ
  | 0 => D.delta0
  | n + 1 => D.toeplitzDet n * D.stepFactor n

/-- The precise determinant product formula. -/
def detProductFactorization (D : XiToeplitzDetVerblunskyData) : Prop :=
  ∀ m ≤ D.steps, D.toeplitzDet m = D.delta0 * Finset.prod (Finset.range m) D.stepFactor

/-- Failure indices where the Verblunsky modulus reaches or exceeds one. -/
def failureSet (D : XiToeplitzDetVerblunskyData) : Set ℕ :=
  {m | ∃ j < D.steps, m = j + 1 ∧ 1 ≤ |D.alphaAt j|}

/-- The first bad Verblunsky coefficient forces the first nonpositive Toeplitz determinant, while
all smaller determinants stay positive. -/
def minimalFailureIndexControl (D : XiToeplitzDetVerblunskyData) : Prop :=
  ∀ m, IsLeast D.failureSet m →
    D.toeplitzDet m ≤ 0 ∧ ∀ r < m, 0 < D.toeplitzDet r

lemma toeplitzDet_product (D : XiToeplitzDetVerblunskyData) :
    ∀ m, D.toeplitzDet m = D.delta0 * Finset.prod (Finset.range m) D.stepFactor
  | 0 => by simp [toeplitzDet]
  | m + 1 => by
      rw [toeplitzDet, toeplitzDet_product D m, Finset.prod_range_succ]
      ring

lemma stepFactor_nonpos_of_bad (D : XiToeplitzDetVerblunskyData) {j : ℕ}
    (hj : 1 ≤ |D.alphaAt j|) : D.stepFactor j ≤ 0 := by
  have hsquare : 1 ≤ D.alphaAt j ^ 2 := by
    have habs_sq : |D.alphaAt j| ^ 2 = D.alphaAt j ^ 2 := by
      rw [sq_abs]
    nlinarith [abs_nonneg (D.alphaAt j)]
  unfold stepFactor
  nlinarith

lemma stepFactor_pos_of_good (D : XiToeplitzDetVerblunskyData) {j : ℕ}
    (hj : |D.alphaAt j| < 1) : 0 < D.stepFactor j := by
  have hsquare : D.alphaAt j ^ 2 < 1 := by
    have habs_sq : |D.alphaAt j| ^ 2 = D.alphaAt j ^ 2 := by
      rw [sq_abs]
    nlinarith [abs_nonneg (D.alphaAt j)]
  unfold stepFactor
  nlinarith

lemma toeplitzDet_pos_of_prefix_good (D : XiToeplitzDetVerblunskyData) {r : ℕ}
    (hgood : ∀ j < r, |D.alphaAt j| < 1) : 0 < D.toeplitzDet r := by
  rw [toeplitzDet_product D r]
  refine mul_pos D.hdelta0 ?_
  refine Finset.prod_pos ?_
  intro j hj
  exact D.stepFactor_pos_of_good (hgood j (Finset.mem_range.mp hj))

lemma detProductFactorization_true (D : XiToeplitzDetVerblunskyData) : D.detProductFactorization := by
  unfold detProductFactorization
  intro m hm
  exact toeplitzDet_product D m

lemma minimalFailureIndexControl_true (D : XiToeplitzDetVerblunskyData) :
    D.minimalFailureIndexControl := by
  intro m hleast
  rcases hleast.1 with ⟨j, hjSteps, rfl, hjBad⟩
  have hprevPos : 0 < D.toeplitzDet j := by
    apply D.toeplitzDet_pos_of_prefix_good
    intro t ht
    have hnotBad : ¬ 1 ≤ |D.alphaAt t| := by
      intro htBad
      have hmem : t + 1 ∈ D.failureSet := by
        refine ⟨t, ?_, rfl, htBad⟩
        exact lt_of_lt_of_le ht (Nat.le_of_lt hjSteps)
      have hleast' := hleast.2 hmem
      omega
    exact lt_of_not_ge hnotBad
  have hfactor_nonpos : D.stepFactor j ≤ 0 := D.stepFactor_nonpos_of_bad hjBad
  have hdet_nonpos : D.toeplitzDet (j + 1) ≤ 0 := by
    simpa [toeplitzDet] using mul_nonpos_of_nonneg_of_nonpos hprevPos.le hfactor_nonpos
  refine ⟨hdet_nonpos, ?_⟩
  intro r hr
  apply D.toeplitzDet_pos_of_prefix_good
  intro t ht
  have hnotBad : ¬ 1 ≤ |D.alphaAt t| := by
    intro htBad
    have hmem : t + 1 ∈ D.failureSet := by
      refine ⟨t, ?_, rfl, htBad⟩
      omega
    have hleast' := hleast.2 hmem
    omega
  exact lt_of_not_ge hnotBad

end XiToeplitzDetVerblunskyData

open XiToeplitzDetVerblunskyData

/-- Paper label: `thm:xi-toeplitz-det-verblunsky`. The Toeplitz determinants admit the exact
reflection-coefficient product formula, and the first Verblunsky coefficient with modulus at least
one marks the first nonpositive determinant while all earlier truncations remain positive. -/
theorem paper_xi_toeplitz_det_verblunsky (D : XiToeplitzDetVerblunskyData) :
    D.detProductFactorization ∧ D.minimalFailureIndexControl := by
  exact ⟨D.detProductFactorization_true, D.minimalFailureIndexControl_true⟩

end

end Omega.Zeta
