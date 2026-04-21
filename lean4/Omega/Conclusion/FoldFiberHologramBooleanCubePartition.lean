import Omega.Conclusion.FoldFiberHardcoreAnnealedConservation

namespace Omega.Conclusion

theorem paper_conclusion_fold_fiber_hologram_boolean_cube_partition (m : Nat) {X : Type*}
    [Fintype X] [DecidableEq X] (fold : Omega.Conclusion.FoldSubset m → X) :
    (∀ omega : Omega.Conclusion.FoldSubset m,
      ∃! x : X, omega ∈ Omega.Conclusion.foldFiber fold x) ∧
      (∀ x y : X, x ≠ y →
        Disjoint (Omega.Conclusion.foldFiber fold x) (Omega.Conclusion.foldFiber fold y)) := by
  constructor
  · intro omega
    refine ⟨fold omega, ?_, ?_⟩
    · simp [Omega.Conclusion.foldFiber]
    · intro x hx
      exact (by simpa [Omega.Conclusion.foldFiber] using hx : fold omega = x).symm
  · intro x y hxy
    refine Finset.disjoint_left.2 ?_
    intro omega hx hy
    exact hxy ((by simpa [Omega.Conclusion.foldFiber] using hx : fold omega = x).symm.trans
      (by simpa [Omega.Conclusion.foldFiber] using hy : fold omega = y))

end Omega.Conclusion
