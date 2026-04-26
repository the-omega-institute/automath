import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-microescort-oracle-capacity-closed-form`.
The paper-facing closed-form proposition for finite fibers: if admissible recovery sets have
fiberwise cardinality at most `min (d x) (2^B)` and the success mass is the micro-escort weighted
fiber sum, then every admissible set is bounded by the closed form, and any admissible set
attaining the fiberwise cardinalities attains the closed form. -/
def paper_conclusion_microescort_oracle_capacity_closed_form
    {X Ω : Type*} [Fintype X] [Fintype Ω] [DecidableEq X] [DecidableEq Ω]
    (Fold : Ω → X) (d : X → ℕ) (a B : ℕ) (successMass : Set Ω → ℝ)
    (admissible : Set Ω → Prop) : Prop := by
  exact
    (∀ S : Set Ω, admissible S →
        successMass S =
          ∑ x : X,
            ((d x : ℝ) ^ (a - 1)) *
              (({ω : Ω | ω ∈ S ∧ Fold ω = x}.ncard : ℝ))) →
      (∀ S : Set Ω, admissible S →
          (∀ x : X, {ω : Ω | ω ∈ S ∧ Fold ω = x}.ncard ≤ min (d x) (2 ^ B)) →
            successMass S ≤
              ∑ x : X, ((d x : ℝ) ^ (a - 1)) * (min (d x) (2 ^ B) : ℝ)) ∧
        ((∃ S : Set Ω,
            admissible S ∧
              ∀ x : X, {ω : Ω | ω ∈ S ∧ Fold ω = x}.ncard = min (d x) (2 ^ B)) →
          ∃ S : Set Ω,
            admissible S ∧
              successMass S =
                ∑ x : X, ((d x : ℝ) ^ (a - 1)) * (min (d x) (2 ^ B) : ℝ))

end Omega.Conclusion
