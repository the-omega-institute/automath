import Mathlib.Tactic

namespace Omega.Conclusion

/-- The paper's closed-form candidate for the inverse entries of the softcore weight matrix. -/
def softcoreWeightMatrixInverseEntry (q r j : ℕ) : ℚ :=
  if r = 0 then
    if j = 0 then (-1 : ℚ) else if j = q then 2 else 0
  else if j < q - r then
    0
  else
    2 * ((-1 : ℚ) ^ (j - (q - r))) * Nat.choose r (q - j)

/-- The softcore weight matrix inverse has the paper's piecewise explicit entry formula for
nontrivial sizes `q > 0`.
    thm:conclusion-softcore-weight-matrix-explicit-inverse -/
theorem paper_conclusion_softcore_weight_matrix_explicit_inverse (q : ℕ) (hq : 0 < q) :
    softcoreWeightMatrixInverseEntry q 0 0 = -1 ∧
    softcoreWeightMatrixInverseEntry q 0 q = 2 ∧
    (∀ j : ℕ, 0 < j → j < q → softcoreWeightMatrixInverseEntry q 0 j = 0) ∧
    (∀ r j : ℕ, 0 < r → j < q - r → softcoreWeightMatrixInverseEntry q r j = 0) ∧
    (∀ r j : ℕ, 0 < r → q - r ≤ j →
      softcoreWeightMatrixInverseEntry q r j =
        2 * ((-1 : ℚ) ^ (j - (q - r))) * Nat.choose r (q - j)) := by
  refine ⟨by simp [softcoreWeightMatrixInverseEntry],
    by simp [softcoreWeightMatrixInverseEntry, hq.ne'], ?_, ?_, ?_⟩
  · intro j hj0 hjq
    simp [softcoreWeightMatrixInverseEntry, hj0.ne', hjq.ne]
  · intro r j hr hj
    simp [softcoreWeightMatrixInverseEntry, hr.ne', hj]
  · intro r j hr hj
    simp [softcoreWeightMatrixInverseEntry, hr.ne', Nat.not_lt.mpr hj]

end Omega.Conclusion
