import Mathlib.Tactic

namespace Omega.EA.StableAddNoNullCreation

/-- Object-layer stable addition does not create a value when either readout is absent.
    prop:stable-add-no-null-creation -/
theorem paper_stable_add_no_null_creation {Address Value : Type*}
    (read : Address -> Option Value) (stableAdd : Value -> Value -> Value) (a b : Address) :
    read a = none \/ read b = none ->
      (read a).bind (fun x => (read b).map (fun y => stableAdd x y)) = none := by
  intro h
  rcases h with ha | hb
  · simp [ha]
  · simp [hb]

end Omega.EA.StableAddNoNullCreation
