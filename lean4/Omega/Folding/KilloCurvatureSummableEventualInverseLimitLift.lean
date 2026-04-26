import Omega.Folding.NaivePrefixLift
import Omega.Folding.SummableDefectsEventualCompatibility

namespace Omega.Folding

open Finset

/-- The curvature event at stage `m` is exactly the restriction compatibility of the stage
`m + 1` and `m` fold states. -/
def killo_curvature_summable_eventual_inverse_limit_lift_curvature_event
    (x : ∀ m : ℕ, Omega.X m) (m : ℕ) : Prop :=
  Omega.X.restrict (x (m + 1)) = x m

/-- Paper label: `prop:killo-curvature-summable-eventual-inverse-limit-lift`. Summable curvature
defects force eventual stagewise compatibility, and the compatible tail therefore lifts to an
inverse-limit point in the stable-word system. -/
theorem paper_killo_curvature_summable_eventual_inverse_limit_lift
    (x : ∀ m : ℕ, Omega.X m) (δMass : ℕ → ℕ) (C : ℕ)
    (hcurvature :
      ∀ m,
        δMass m = 0 ↔
          killo_curvature_summable_eventual_inverse_limit_lift_curvature_event x m)
    (hbd : ∀ n, ∑ i ∈ Finset.range n, δMass i ≤ C) :
    (∃ M,
      ∀ m, M ≤ m →
        killo_curvature_summable_eventual_inverse_limit_lift_curvature_event x m) ∧
      ∃ M : ℕ, ∃ xInf : Omega.X.XInfinity, ∀ m, M ≤ m → Omega.X.prefixWord xInf m = x m := by
  let Lift : Prop :=
    ∃ M,
      ∀ m, M ≤ m →
        killo_curvature_summable_eventual_inverse_limit_lift_curvature_event x m
  have hcompat :=
    paper_fold_truncation_summable_defects_eventual_compatibility
      δMass
      (killo_curvature_summable_eventual_inverse_limit_lift_curvature_event x)
      Lift
      hcurvature
      (by
        unfold Lift
        constructor
        · rintro ⟨M, hM⟩
          exact ⟨M, fun m hm => (hcurvature m).mp (hM m hm)⟩
        · rintro ⟨M, hM⟩
          exact ⟨M, fun m hm => (hcurvature m).mpr (hM m hm)⟩)
  have htailZero : ∃ M, ∀ m, M ≤ m → δMass m = 0 :=
    hcompat.1.1 ⟨C, hbd⟩
  have htailCompat : Lift :=
    hcompat.2.2.mp htailZero
  have hlift :
      ∃ M : ℕ, ∃ xInf : Omega.X.XInfinity, ∀ m, M ≤ m → Omega.X.prefixWord xInf m = x m :=
    Omega.Folding.NaivePrefixLift.paper_fold_naive_prefix_lift x δMass C hcurvature hbd
  exact ⟨htailCompat, hlift⟩

end Omega.Folding
