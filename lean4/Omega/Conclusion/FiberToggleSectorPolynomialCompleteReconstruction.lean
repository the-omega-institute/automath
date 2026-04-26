import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic
import Omega.Conclusion.FiberToggleBooleanSpectrumPolynomial
import Omega.POM.FiberReconstructionAutGroup
import Omega.POM.FiberReconstructionCartesianProduct

namespace Omega.Conclusion

noncomputable section

/-- The shifted Fibonacci component sizes attached to a path-length list. -/
def conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes
    (lengths : List Nat) : List Nat :=
  lengths.map fun ell => Nat.fib (ell + 2)

/-- The sector polynomial obtained by feeding the Fibonacci component sizes into the Boolean
spectrum polynomial from the previous theorem. -/
noncomputable def conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial
    (lengths : List Nat) : Polynomial ℤ :=
  toggleBooleanSpectrumPolynomial
    (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths)

/-- The paper-facing wrapper keeps the sector polynomial, the shifted-Fibonacci encoding of path
lengths, and the previously verified Cartesian-product and automorphism packages in one place. -/
def conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_statement
    (lengths1 lengths2 : List Nat) : Prop :=
  (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial lengths1 =
      conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial lengths2 →
      ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths1).map
          fun n => (n : ℤ)).prod =
        ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes
          lengths2).map fun n => (n : ℤ)).prod) ∧
    (∀ a b : ℕ, Nat.fib (a + 2) = Nat.fib (b + 2) → a = b) ∧
    Omega.POM.FiberReconstructionCartesianFactors lengths1 ∧
    Omega.POM.FiberReconstructionCartesianFactors lengths2 ∧
    Fintype.card (Omega.POM.FiberReconstructionAutModel lengths1) =
      2 ^ lengths1.length *
        Finset.prod (lengths1.eraseDups.toFinset) (fun ell => Nat.factorial (lengths1.count ell)) ∧
    Fintype.card (Omega.POM.FiberReconstructionAutModel lengths2) =
      2 ^ lengths2.length *
        Finset.prod (lengths2.eraseDups.toFinset) (fun ell => Nat.factorial (lengths2.count ell))

private theorem
    conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_eval_one_of_eq
    {lengths1 lengths2 : List Nat}
    (hpoly :
      conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial lengths1 =
        conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial
          lengths2) :
    ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths1).map
        fun n => (n : ℤ)).prod =
      ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths2).map
        fun n => (n : ℤ)).prod := by
  have hEval :=
    congrArg (fun p : Polynomial ℤ => p.eval 1) hpoly
  have h1 :
      (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial
          lengths1).eval 1 =
        ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes
          lengths1).map fun n => (n : ℤ)).prod := by
    simpa [conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial,
      conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes] using
      (paper_conclusion_fiber_toggle_boolean_spectrum_polynomial
        (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths1)).2.2.2
  have h2 :
      (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial
          lengths2).eval 1 =
        ((conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes
          lengths2).map fun n => (n : ℤ)).prod := by
    simpa [conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_sector_polynomial,
      conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes] using
      (paper_conclusion_fiber_toggle_boolean_spectrum_polynomial
        (conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fiber_sizes lengths2)).2.2.2
  simpa [h1, h2] using hEval

private theorem conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fib_injective :
    ∀ a b : ℕ, Nat.fib (a + 2) = Nat.fib (b + 2) → a = b := by
  intro a b hab
  exact Nat.fib_add_two_strictMono.injective hab

/-- Paper label: `thm:conclusion-fiber-toggle-sector-polynomial-complete-reconstruction`. -/
theorem paper_conclusion_fiber_toggle_sector_polynomial_complete_reconstruction
    (lengths1 lengths2 : List Nat) :
    conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_statement lengths1 lengths2 := by
  refine ⟨
    (fun hpoly =>
      conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_eval_one_of_eq hpoly),
    conclusion_fiber_toggle_sector_polynomial_complete_reconstruction_fib_injective,
    (Omega.POM.paper_pom_fiber_reconstruction_cartesian_product lengths1).1,
    (Omega.POM.paper_pom_fiber_reconstruction_cartesian_product lengths2).1,
    (Omega.POM.paper_pom_fiber_reconstruction_aut_group lengths1).2.2.2,
    (Omega.POM.paper_pom_fiber_reconstruction_aut_group lengths2).2.2.2⟩

end

end Omega.Conclusion
