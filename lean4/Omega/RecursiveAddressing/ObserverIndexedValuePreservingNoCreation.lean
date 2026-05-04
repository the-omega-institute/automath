namespace Omega.RecursiveAddressing

/-- Paper-facing seed: a single value-preserving rewrite step cannot create a
    new observer-indexed value out of an undefined source.
    prop:observer-indexed-value-preserving-no-creation -/
theorem paper_recursive_addressing_observer_indexed_value_preserving_no_creation
    {Expr State Value : Type}
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {t t' : Expr}
    (hstep : step t t')
    (ht : readout p t = none) :
    readout p t' = none := by
  cases hread : readout p t' with
  | none =>
      rfl
  | some v =>
      have hsrc : readout p t = some v := hpres hstep hread
      rw [ht] at hsrc
      cases hsrc

/-- Paper label: `prop:observer-indexed-value-preserving-no-creation`. -/
theorem paper_observer_indexed_value_preserving_no_creation {Expr State Value : Type}
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {t t' : Expr}
    (hstep : step t t')
    (ht : readout p t = none) :
    readout p t' = none := by
  exact paper_recursive_addressing_observer_indexed_value_preserving_no_creation
    readout step hpres hstep ht

end Omega.RecursiveAddressing
