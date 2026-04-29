import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-euler-surgery-cofinal-tail-rigidity`. -/
theorem paper_conclusion_finite_euler_surgery_cofinal_tail_rigidity
    (p pCore : Nat → ℚ) (logM logMCore u zStar : ℚ) (ell E m N : Nat)
    (hm : 1 ≤ m) (hell : 1 ≤ ell) (hN : ell < N)
    (hcoeff_ne : ∀ n, n ≠ ell → p n = pCore n)
    (hcoeff_ell : p ell = pCore ell + (m : ℚ) * u ^ E)
    (hlog : logM = logMCore + (m : ℚ) * u ^ E * zStar ^ ell) :
    (logM = logMCore + (m : ℚ) * u ^ E * zStar ^ ell) ∧
      ∀ n, N ≤ n → p n = pCore n := by
  let _ := hm
  let _ := hell
  let _ := hcoeff_ell
  refine ⟨hlog, ?_⟩
  intro n hn
  exact hcoeff_ne n (by omega)

end Omega.Conclusion
