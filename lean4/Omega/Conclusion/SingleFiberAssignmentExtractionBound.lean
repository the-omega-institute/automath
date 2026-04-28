import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- Paper label: `cor:conclusion-single-fiber-assignment-extraction-bound`. -/
theorem paper_conclusion_single_fiber_assignment_extraction_bound
    {n L : ℕ} {Fx Code : Type*} [Fintype Fx] [Fintype Code]
    (hFx : Fintype.card Fx = 2 ^ n) (hCode : Fintype.card Code ≤ 2 ^ L)
    (E : Fx → Code) (D : Code → Fx) :
    Fintype.card {x : Fx // D (E x) = x} ≤ 2 ^ L := by
  classical
  have _ : Fintype.card Fx = 2 ^ n := hFx
  have hInjective :
      Function.Injective (fun x : {x : Fx // D (E x) = x} => E x.1) := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = D (E x.1) := x.2.symm
      _ = D (E y.1) := congrArg D hxy
      _ = y.1 := y.2
  exact (Fintype.card_le_of_injective _ hInjective).trans hCode

end Omega.Conclusion
