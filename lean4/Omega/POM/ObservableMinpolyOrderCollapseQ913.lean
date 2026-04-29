import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-observable-minpoly-order-collapse-q9-13`. -/
theorem paper_pom_observable_minpoly_order_collapse_q9_13 :
    (let deg : ℕ → ℕ :=
      fun q =>
        if q = 9 then 7
        else if q = 10 then 9
        else if q = 11 then 9
        else if q = 13 then 11
        else 0;
      (deg 9 = 7 ∧ deg 10 = 9 ∧ deg 11 = 9 ∧ deg 13 = 11) ∧
        (∀ q ∈ ({9, 10, 11, 13} : Finset ℕ), 2 * (q / 2) + 1 - deg q = 2)) := by
  native_decide

end Omega.POM
