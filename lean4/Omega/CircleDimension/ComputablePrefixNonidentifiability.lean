import Omega.CircleDimension.ComputablePrefixNonidentifiabilityMultiplicity

namespace Omega.CircleDimension

/-- Paper-facing single-competitor specialization of the finite-prefix nonidentifiability
package. The competitor agrees on the shared prefix, flips the next bit, and keeps the same
complexity overhead bound.
    thm:cdim-computable-prefix-nonidentifiability -/
theorem paper_cdim_computable_prefix_nonidentifiability
    (Kgen : (ℕ → Bool) → ℕ) (x : ℕ → Bool) (n C : ℕ)
    (hC :
      Kgen
          (fun m =>
            if m < n then
              x m
            else if m = n then
              !(x n)
            else
              false) ≤
        Kgen x + C) :
    ∃ y : ℕ → Bool,
      (∀ m, m < n → y m = x m) ∧
        y n = !(x n) ∧
        y ≠ x ∧
        Kgen y ≤ Kgen x + C := by
  have hMultiplicity :=
    paper_cdim_computable_prefix_nonidentifiability_multiplicity Kgen x n 1 C (by decide)
      (by
        intro j
        fin_cases j
        simpa using hC)
  let y : ℕ → Bool := fun m =>
    if m < n then
      x m
    else if m = n then
      !(x n)
    else
      false
  refine ⟨y, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    simp [y, hm]
  · simp [y]
  · intro hEq
    have hAt : y n = x n := congrFun hEq n
    by_cases hx : x n
    · simp [y, hx] at hAt
    · simp [y, hx] at hAt
  · simpa [y] using hC

end Omega.CircleDimension
