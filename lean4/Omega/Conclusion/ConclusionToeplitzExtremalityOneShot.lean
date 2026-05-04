import Mathlib.Tactic

namespace Omega.Conclusion

/-- Support cardinality of the positive uniform regular polygon forced by order `N`. -/
def conclusion_toeplitz_extremality_one_shot_polygon_support_card (N : Nat) : Nat :=
  N + 1

/-- Equality of two polygon extremizers forces equality of their support cardinalities. -/
def conclusion_toeplitz_extremality_one_shot_same_polygon_support (N M : Nat) : Prop :=
  conclusion_toeplitz_extremality_one_shot_polygon_support_card N =
    conclusion_toeplitz_extremality_one_shot_polygon_support_card M

/-- Concrete one-shot extremality claim: two distinct orders cannot have the same forced
regular-polygon support cardinality. -/
def conclusion_toeplitz_extremality_one_shot_claim (N M : Nat) : Prop :=
  N ≠ M → ¬ conclusion_toeplitz_extremality_one_shot_same_polygon_support N M

/-- Paper label: `cor:conclusion-toeplitz-extremality-one-shot`. -/
theorem paper_conclusion_toeplitz_extremality_one_shot (N M : Nat) :
    conclusion_toeplitz_extremality_one_shot_claim N M := by
  intro hNM hcard
  apply hNM
  exact Nat.succ.inj hcard

end Omega.Conclusion
