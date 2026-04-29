import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-haar-zero-universality-fixed-prime-ledger-decoupling`. -/
theorem paper_conclusion_haar_zero_universality_fixed_prime_ledger_decoupling
    (HaarLimit : (ℕ → ℕ → ℤ) → Prop) (ampDist : (ℕ → ℤ) → (ℕ → ℤ) → ℝ)
    (p0 : ℕ) (a b : ℤ) (q : ℕ → ℕ) (_hab : a ≠ b)
    (huniv : ∀ c : ℤ,
      HaarLimit (fun N p => if p = p0 then c else if p = q N then 1 else 0))
    (hrigid : ∀ r s : ℕ → ℤ,
      Real.sqrt Real.pi * |((r p0 - s p0 : ℤ) : ℝ)| ≤ ampDist r s) :
    HaarLimit (fun N p => if p = p0 then a else if p = q N then 1 else 0) ∧
      HaarLimit (fun N p => if p = p0 then b else if p = q N then 1 else 0) ∧
      ∀ N,
        Real.sqrt Real.pi * |((a - b : ℤ) : ℝ)| ≤
          ampDist
            (fun p => if p = p0 then a else if p = q N then 1 else 0)
            (fun p => if p = p0 then b else if p = q N then 1 else 0) := by
  refine ⟨huniv a, huniv b, ?_⟩
  intro N
  simpa using
    hrigid
      (fun p => if p = p0 then a else if p = q N then 1 else 0)
      (fun p => if p = p0 then b else if p = q N then 1 else 0)

end Omega.Conclusion
