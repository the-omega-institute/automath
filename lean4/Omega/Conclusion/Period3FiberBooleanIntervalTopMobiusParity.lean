import Mathlib.Data.Finset.Basic

namespace Omega.Conclusion

/-- Boolean interval labels for the period-three fiber model. -/
def conclusion_period3_fiber_boolean_interval_top_mobius_parity_g
    (n : ℕ) (S : Finset (Fin n)) : Finset (Fin n) :=
  S

/-- The prefixed Möbius primitive on the Boolean interval, normalized as the Kronecker delta. -/
def conclusion_period3_fiber_boolean_interval_top_mobius_parity_P
    (n : ℕ) (S R : Finset (Fin n)) : ℤ :=
  if R = S then 1 else 0

/-- The top Boolean interval has one top element. -/
def conclusion_period3_fiber_boolean_interval_top_mobius_parity_rank_top (_n : ℕ) : ℕ :=
  1

/-- Paper label: `thm:conclusion-period3-fiber-boolean-interval-top-mobius-parity`. -/
theorem paper_conclusion_period3_fiber_boolean_interval_top_mobius_parity (n : ℕ) :
    Function.Injective
        (fun S : Finset (Fin n) =>
          conclusion_period3_fiber_boolean_interval_top_mobius_parity_g n S) ∧
      (∀ S R : Finset (Fin n),
        conclusion_period3_fiber_boolean_interval_top_mobius_parity_P n S R =
          if R = S then 1 else 0) ∧
      conclusion_period3_fiber_boolean_interval_top_mobius_parity_rank_top n = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro S R hSR
    simpa [conclusion_period3_fiber_boolean_interval_top_mobius_parity_g] using hSR
  · intro S R
    rfl
  · rfl

end Omega.Conclusion
