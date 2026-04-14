namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a finite normalization chain of value-preserving rewrites cannot create
    a new non-null readout at the end of the chain.
    cor:normalization-no-fact-creation -/
theorem paper_conservative_extension_normalization_no_fact_creation_seeds
    {Expr State Value : Type}
    (readout : State → Expr → Option Value) (p : State)
    {n : Nat} (E : Nat → Expr)
    (hstep : ∀ i, i < n → ∀ v, readout p (E (i + 1)) = some v → readout p (E i) = some v)
    {v : Value}
    (hend : readout p (E n) = some v) :
    readout p (E 0) = some v := by
  induction n generalizing E with
  | zero =>
      simpa using hend
  | succ n ih =>
      have hprev : readout p (E n) = some v :=
        hstep n (Nat.lt_succ_self n) v hend
      have hstep' :
          ∀ i, i < n → ∀ w, readout p (E (i + 1)) = some w → readout p (E i) = some w := by
        intro i hi w hw
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)) w hw
      exact ih E hstep' hprev

end Omega.LogicExpansionChain
