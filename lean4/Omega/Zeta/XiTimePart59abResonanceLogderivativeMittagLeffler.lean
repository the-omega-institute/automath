import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part59ab-resonance-logderivative-mittagleffler`. -/
theorem paper_xi_time_part59ab_resonance_logderivative_mittagleffler
    (finiteIter tailControl principalValueExpansion : Prop) (iterStep : ℕ → Prop)
    (hbase : iterStep 2) (hsucc : ∀ N, 2 ≤ N → iterStep N → iterStep (N + 1))
    (hfinite : (∀ N, 2 ≤ N → iterStep N) → finiteIter) (htail : finiteIter → tailControl)
    (hpv : tailControl → principalValueExpansion) :
    finiteIter ∧ tailControl ∧ principalValueExpansion := by
  have hall : ∀ N, 2 ≤ N → iterStep N := by
    refine Nat.le_induction ?base ?step
    · exact hbase
    · intro N hN hiter
      exact hsucc N hN hiter
  have hfin : finiteIter := hfinite hall
  have htailControl : tailControl := htail hfin
  exact ⟨hfin, htailControl, hpv htailControl⟩

end Omega.Zeta
