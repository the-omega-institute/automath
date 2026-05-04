import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-smith-finite-stage-finite-jet-joint-fiber-countably-infinite`. -/
theorem paper_conclusion_smith_finite_stage_finite_jet_joint_fiber_countably_infinite
    {Completion Observation : Type*} (O : Completion -> Observation) (y : Observation)
    (orbit : Nat -> Completion) (hinj : Function.Injective orbit)
    (hconst : ∀ n : Nat, O (orbit n) = y) : Infinite {x : Completion // O x = y} := by
  apply Infinite.of_injective
    (fun n : Nat => (⟨orbit n, hconst n⟩ : {x : Completion // O x = y}))
  intro m n hmn
  exact hinj (congrArg Subtype.val hmn)

end Omega.Conclusion
