import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing successor-orbit normal form: the valuation identifies every element with the
corresponding iterate of the successor from the distinguished zero state.
    thm:conclusion-stable-successor-orbit-normal-form -/
theorem paper_conclusion_stable_successor_orbit_normal_form {X : Type*} (zeroX : X) (S : X → X)
    (Val : X → ℕ) (hzero : Val zeroX = 0) (hstep : ∀ c, Val (S c) = Val c + 1)
    (hbij : Function.Bijective Val) (c : X) :
    c = (S^[Val c]) zeroX := by
  have hiter : ∀ n : ℕ, Val ((S^[n]) zeroX) = n := by
    intro n
    induction n with
    | zero =>
        simpa using hzero
    | succ n ih =>
        rw [Function.iterate_succ_apply', hstep, ih]
  apply hbij.1
  symm
  exact hiter (Val c)

end Omega.Conclusion
