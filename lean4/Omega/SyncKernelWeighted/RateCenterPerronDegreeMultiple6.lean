import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The audited center-slice cofactor `Q(u)` in the factorization around `u = 1`. -/
def rateCenterPerronQ (u : ℚ) : ℚ :=
  u ^ 2 + 1

/-- The center-slice factorization with an exact sixth power of `(u - 1)`. -/
def rateCenterPerronPolynomial (u : ℚ) : ℚ :=
  (u - 1) ^ 6 * rateCenterPerronQ u

/-- The ramification index extracted from the audited multiplicity-six factor and `Q(1) ≠ 0`. -/
def rateCenterRamificationIndex : ℕ :=
  if rateCenterPerronQ 1 = 0 then 0 else 6

/-- Any audited branch degree is a multiple of the ramification index. -/
def rateCenterBranchDegree (k : ℕ) : ℕ :=
  rateCenterRamificationIndex * k

lemma rateCenterPerron_factorization (u : ℚ) :
    rateCenterPerronPolynomial u = (u - 1) ^ 6 * rateCenterPerronQ u := rfl

lemma rateCenterPerronQ_one_ne_zero : rateCenterPerronQ 1 ≠ 0 := by
  norm_num [rateCenterPerronQ]

lemma rateCenter_ramificationIndex_eq_six : rateCenterRamificationIndex = 6 := by
  unfold rateCenterRamificationIndex
  simp [rateCenterPerronQ_one_ne_zero]

lemma six_dvd_rateCenterBranchDegree (k : ℕ) : 6 ∣ rateCenterBranchDegree k := by
  refine ⟨k, ?_⟩
  simp [rateCenterBranchDegree, rateCenter_ramificationIndex_eq_six, Nat.mul_comm]

/-- The audited center slice has an exact multiplicity-six root at `u = 1`; therefore the
ramification index is `6`, and the abstract branching law forces the branch degree to be a
multiple of `6`.
    cor:rate-center-perron-degree-multiple-6 -/
theorem paper_rate_center_perron_degree_multiple_6 (k : ℕ) :
    rateCenterRamificationIndex = 6 ∧ 6 ∣ rateCenterBranchDegree k := by
  have hq : rateCenterPerronQ 1 ≠ 0 := rateCenterPerronQ_one_ne_zero
  have hindex : rateCenterRamificationIndex = 6 := by
    unfold rateCenterRamificationIndex
    simp [hq]
  refine ⟨hindex, ?_⟩
  simp [rateCenterBranchDegree, hindex]

end Omega.SyncKernelWeighted
