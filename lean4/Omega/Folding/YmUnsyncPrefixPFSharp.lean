/-- Paper-facing wrapper for the finite synchronization-tail construction and its
    Perron--Frobenius sharp exponent limit.
    thm:Ym-unsync-prefix-pf-sharp -/
theorem paper_ym_unsync_prefix_pf_sharp (m : Nat) (pfSharp exponentLimit : Prop)
    (hSharp : pfSharp) (hLimit : pfSharp -> exponentLimit) : exponentLimit := by
  let _ := m
  exact hLimit hSharp
