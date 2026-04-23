import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The minimal common Fibonacci conductor carried by a finite depth family. -/
noncomputable def conclusion_fibadic_finite_depth_family_algebra_closure_lcm
    (D : Finset ℕ) : ℕ :=
  Finset.lcm D Nat.fib

/-- In the seed model, saying that a finite quotient `A_N` contains every depth-`e` generator just
means that each Fibonacci modulus `F_e` divides `N`. -/
def conclusion_fibadic_finite_depth_family_algebra_closure_common_host
    (D : Finset ℕ) (N : ℕ) : Prop :=
  ∀ e ∈ D, Nat.fib e ∣ N

/-- Paper label: `thm:conclusion-fibadic-finite-depth-family-algebra-closure`.
This finite-conductor wrapper records the two inclusions in the paper proof as the universal
property of the lcm conductor: every depth generator factors through the common host
`lcm {F_e : e ∈ D}`, and any other common host is a multiple of that lcm. The finite quotient
`A_L` therefore has its canonical `L`-element basis. -/
theorem paper_conclusion_fibadic_finite_depth_family_algebra_closure (D : Finset ℕ) :
    conclusion_fibadic_finite_depth_family_algebra_closure_common_host D
      (conclusion_fibadic_finite_depth_family_algebra_closure_lcm D) ∧
    (∀ N,
      conclusion_fibadic_finite_depth_family_algebra_closure_common_host D N ↔
        conclusion_fibadic_finite_depth_family_algebra_closure_lcm D ∣ N) ∧
    Fintype.card
        (Fin (conclusion_fibadic_finite_depth_family_algebra_closure_lcm D)) =
      conclusion_fibadic_finite_depth_family_algebra_closure_lcm D := by
  refine ⟨?_, ?_, by simp [conclusion_fibadic_finite_depth_family_algebra_closure_lcm]⟩
  · intro e he
    exact Finset.dvd_lcm he
  · intro N
    constructor
    · intro hN
      exact Finset.lcm_dvd (fun e he => hN e he)
    · intro hL e he
      exact dvd_trans (Finset.dvd_lcm he) hL

end Omega.Conclusion
