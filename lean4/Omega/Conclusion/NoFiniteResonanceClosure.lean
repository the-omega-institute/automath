import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- The finite resonance skeleton obtained by truncating the squared collision profile at level
`U`. -/
noncomputable def finiteResonanceSkeleton (Cphi : ℕ → ℝ) (U : ℕ) : ℝ :=
  1 + 2 * Finset.sum (Finset.range (U + 1)) (fun u => (Cphi u) ^ 2)

/-- If every finite resonance skeleton is dominated by some scaled collision term and the skeletons
are unbounded, then the scaled collision terms are themselves unbounded.
    thm:conclusion-no-finite-resonance-closure -/
theorem paper_conclusion_no_finite_resonance_closure (Cphi Col : ℕ → ℝ)
    (hLower : ∀ U : ℕ, ∃ m : ℕ, finiteResonanceSkeleton Cphi U ≤ (Nat.fib (m + 2) : ℝ) * Col m)
    (hUnbounded : ∀ B : ℝ, ∃ U : ℕ, B ≤ finiteResonanceSkeleton Cphi U) :
    ∀ B : ℝ, ∃ m : ℕ, B ≤ (Nat.fib (m + 2) : ℝ) * Col m := by
  intro B
  obtain ⟨U, hU⟩ := hUnbounded B
  obtain ⟨m, hm⟩ := hLower U
  exact ⟨m, hU.trans hm⟩

end Omega.Conclusion
