import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hidden-subgroup-determines-anomaly-minimal-alphabet`. -/
theorem paper_conclusion_hidden_subgroup_determines_anomaly_minimal_alphabet
    {A Sigma : Type*} [Fintype A] [Fintype Sigma]
    (readout : A -> Sigma) (hfaithful : Function.Injective readout) (k : Nat)
    (hbits : Fintype.card Sigma ≤ 2 ^ k) :
    Fintype.card A ≤ 2 ^ k := by
  exact (Fintype.card_le_of_injective readout hfaithful).trans hbits

end Omega.Conclusion
