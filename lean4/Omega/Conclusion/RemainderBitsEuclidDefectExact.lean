import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete remainder-bit data: each fiber contributes a remainder level `s_x ∈ [0, M]`. -/
structure ConclusionRemainderBitsEuclidDefectData where
  Fiber : Type
  instFintypeFiber : Fintype Fiber
  s : Fiber → ℝ
  M : ℝ
  hM : 0 < M
  hbox : ∀ x, 0 ≤ s x ∧ s x ≤ M

attribute [instance] ConclusionRemainderBitsEuclidDefectData.instFintypeFiber

/-- Fiberwise second-order Euclid defect. -/
def remainderBitsFiberEuclidDefect (D : ConclusionRemainderBitsEuclidDefectData)
    (x : D.Fiber) : ℝ :=
  D.s x - D.s x ^ 2 / D.M

/-- The total defect obtained by summing over all fibers. -/
def remainderBitsTotalEuclidDefect (D : ConclusionRemainderBitsEuclidDefectData) : ℝ :=
  ∑ x, remainderBitsFiberEuclidDefect D x

/-- The linear remainder term isolated from the fiberwise identity. -/
def remainderBitsEuclidRemainderTerm (D : ConclusionRemainderBitsEuclidDefectData) : ℝ :=
  ∑ x, D.s x

/-- The quadratic correction isolated from the fiberwise identity. -/
def remainderBitsQuadraticCorrection (D : ConclusionRemainderBitsEuclidDefectData) : ℝ :=
  (∑ x, D.s x ^ 2) / D.M

/-- Paper-facing exact remainder-bits defect statement. -/
def ConclusionRemainderBitsEuclidDefectExactStatement
    (D : ConclusionRemainderBitsEuclidDefectData) : Prop :=
  remainderBitsTotalEuclidDefect D =
      remainderBitsEuclidRemainderTerm D - remainderBitsQuadraticCorrection D ∧
    0 ≤ remainderBitsTotalEuclidDefect D ∧
    remainderBitsTotalEuclidDefect D ≤ (Fintype.card D.Fiber : ℝ) * D.M / 4

private lemma remainderBitsFiberEuclidDefect_nonneg
    (D : ConclusionRemainderBitsEuclidDefectData) (x : D.Fiber) :
    0 ≤ remainderBitsFiberEuclidDefect D x := by
  rcases D.hbox x with ⟨hs0, hsM⟩
  have hM0 : D.M ≠ 0 := ne_of_gt D.hM
  have hrepr :
      remainderBitsFiberEuclidDefect D x = D.s x * (D.M - D.s x) / D.M := by
    unfold remainderBitsFiberEuclidDefect
    field_simp [hM0]
  rw [hrepr]
  have hnum : 0 ≤ D.s x * (D.M - D.s x) := by nlinarith
  exact div_nonneg hnum (le_of_lt D.hM)

private lemma remainderBitsFiberEuclidDefect_le_quarter
    (D : ConclusionRemainderBitsEuclidDefectData) (x : D.Fiber) :
    remainderBitsFiberEuclidDefect D x ≤ D.M / 4 := by
  have hM0 : D.M ≠ 0 := ne_of_gt D.hM
  have hrepr :
      remainderBitsFiberEuclidDefect D x =
        D.M / 4 - (D.s x - D.M / 2) ^ 2 / D.M := by
    unfold remainderBitsFiberEuclidDefect
    field_simp [hM0]
    ring
  rw [hrepr]
  have hnonneg : 0 ≤ (D.s x - D.M / 2) ^ 2 / D.M := by
    exact div_nonneg (sq_nonneg _) (le_of_lt D.hM)
  linarith

/-- Paper label: `thm:conclusion-remainder-bits-euclid-defect-exact`. -/
theorem paper_conclusion_remainder_bits_euclid_defect_exact
    (D : ConclusionRemainderBitsEuclidDefectData) :
    ConclusionRemainderBitsEuclidDefectExactStatement D := by
  refine ⟨?_, ?_, ?_⟩
  · unfold remainderBitsTotalEuclidDefect remainderBitsEuclidRemainderTerm
    unfold remainderBitsQuadraticCorrection remainderBitsFiberEuclidDefect
    calc
      ∑ x, (D.s x - D.s x ^ 2 / D.M)
          = (∑ x, D.s x) - ∑ x, D.s x ^ 2 / D.M := by rw [Finset.sum_sub_distrib]
      _ = (∑ x, D.s x) - (∑ x, D.s x ^ 2) / D.M := by
            have hsum :
                ∑ x, D.s x ^ 2 / D.M = (∑ x, D.s x ^ 2) / D.M := by
              simp [div_eq_mul_inv, Finset.sum_mul]
            rw [hsum]
  · unfold remainderBitsTotalEuclidDefect
    exact Finset.sum_nonneg (fun x hx => remainderBitsFiberEuclidDefect_nonneg D x)
  · unfold remainderBitsTotalEuclidDefect
    calc
      ∑ x, remainderBitsFiberEuclidDefect D x ≤ ∑ x, D.M / 4 := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact remainderBitsFiberEuclidDefect_le_quarter D x
      _ = (Fintype.card D.Fiber : ℝ) * (D.M / 4) := by simp
      _ = (Fintype.card D.Fiber : ℝ) * D.M / 4 := by ring

end

end Omega.Conclusion
