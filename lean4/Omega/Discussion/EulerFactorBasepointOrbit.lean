import Omega.Zeta.CyclicEulerProduct

namespace Omega.Discussion

/-- The primitive Euler factor attached to a basepoint `α` and an orbit of length `n`. -/
def basepointOrbitFactor (n : ℕ) (α r : ℤ) : ℤ :=
  1 - (α * r) ^ n

/-- The multiplicity-`m` orbit block contributes the `m`-th power of the primitive orbit factor.
-/
def basepointOrbitBlockFactor (n m : ℕ) (α r : ℤ) : ℤ :=
  basepointOrbitFactor n α r ^ m

/-- Each cyclic Euler block from the discussion package contributes exactly the orbit factor of a
single basepoint together with its full unit-root orbit; multiplicity `m` is recorded by the
`m`-th power of the primitive factor.
    cor:discussion-euler-factor-is-basepoint-orbit -/
theorem paper_discussion_euler_factor_is_basepoint_orbit (α r : ℤ) (m : ℕ) :
    ((1 - (α * r) • Omega.Zeta.cyclicPerm2).det) ^ m = basepointOrbitBlockFactor 2 m α r ∧
    ((1 - (α * r) • Omega.Zeta.cyclicPerm3).det) ^ m = basepointOrbitBlockFactor 3 m α r ∧
    ((1 - (α * r) • Omega.Zeta.cyclicPerm4).det) ^ m = basepointOrbitBlockFactor 4 m α r ∧
    ((1 - (α * r) • Omega.Zeta.cyclicPerm5).det) ^ m = basepointOrbitBlockFactor 5 m α r ∧
    ((1 - (α * r) • Omega.Zeta.cyclicPerm6).det) ^ m = basepointOrbitBlockFactor 6 m α r := by
  rcases Omega.Zeta.paper_cyclic_euler_product α r with ⟨h2, h3, h4, h5, h6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [basepointOrbitBlockFactor, basepointOrbitFactor] using
      congrArg (fun x : ℤ => x ^ m) h2
  · simpa [basepointOrbitBlockFactor, basepointOrbitFactor] using
      congrArg (fun x : ℤ => x ^ m) h3
  · simpa [basepointOrbitBlockFactor, basepointOrbitFactor] using
      congrArg (fun x : ℤ => x ^ m) h4
  · simpa [basepointOrbitBlockFactor, basepointOrbitFactor] using
      congrArg (fun x : ℤ => x ^ m) h5
  · simpa [basepointOrbitBlockFactor, basepointOrbitFactor] using
      congrArg (fun x : ℤ => x ^ m) h6

end Omega.Discussion
