import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-hellinger-generator-reversibility-dirichlet`. -/
theorem paper_conclusion_hellinger_generator_reversibility_dirichlet
    {X : Type*} [Fintype X] [DecidableEq X]
    (w s : X -> Real) (Q : X -> X -> Real) (A : Real)
    (hoff : forall x y, x ≠ y -> w x * Q x y = s x * s y / (A ^ 2 - 1)) :
    (forall x y, x ≠ y -> w x * Q x y = w y * Q y x) := by
  intro x y hxy
  calc
    w x * Q x y = s x * s y / (A ^ 2 - 1) := hoff x y hxy
    _ = s y * s x / (A ^ 2 - 1) := by rw [mul_comm (s x) (s y)]
    _ = w y * Q y x := (hoff y x (Ne.symm hxy)).symm

end Omega.Conclusion
