import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-period3-fiber-single-stability-complete-boolean-carrier`. -/
theorem paper_conclusion_period3_fiber_single_stability_complete_boolean_carrier {n : Nat}
    (F : (Fin n -> Bool) -> Bool) :
    ∃ encode : (Fin n -> Bool) -> Fin (3 * n) -> Bool,
      ∃ Psi : (Fin (3 * n) -> Bool) -> Bool,
        (∀ y, Psi (encode y) = F y) ∧ Function.Injective encode := by
  let encode : (Fin n -> Bool) -> Fin (3 * n) -> Bool :=
    fun y i => if h : (i : Nat) < n then y ⟨i, h⟩ else false
  let Psi : (Fin (3 * n) -> Bool) -> Bool :=
    fun w => F fun j => w ⟨j, by omega⟩
  refine ⟨encode, Psi, ?_, ?_⟩
  · intro y
    dsimp [Psi, encode]
    congr
    funext j
    simp [j.isLt]
  · intro y z h
    funext j
    have hpoint := congrFun h (⟨j, by omega⟩ : Fin (3 * n))
    simpa [encode, j.isLt] using hpoint

end Omega.Conclusion
