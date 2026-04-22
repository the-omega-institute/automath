import Mathlib.Tactic
import Omega.Conclusion.FiniteFieldJordanExponentPeriodBound
import Omega.Conclusion.ResonanceWindowMod2BinomialCollapse

namespace Omega.Conclusion

open scoped BigOperators fwdDiff

/-- Concrete Hensel-splitting package for the resonance-window parity decomposition. The parity
observable is the sum of a nilpotent shadow, which dies after the audited transient, and a
unipotent mod-`2` tail controlled by the existing binomial/Jordan packages. -/
structure conclusion_resonance_z2_unipotent_complete_parity_data where
  a_q : ℕ
  b_q : ℕ
  k : ℕ
  m0 : ℕ
  nilpotentPart : ℕ → ZMod 2
  unipotentPart : ℕ → ZMod 2
  periodPolynomial : Polynomial (ZMod 2)
  nilpotent_dies : ∀ n ≥ a_q * k, nilpotentPart n = 0
  unipotent_delta_nilpotent :
    ∀ n ≥ m0, Nat.iterate forwardDiff b_q unipotentPart n = 0
  unipotent_eventually_annihilated :
    EventuallyAnnihilatedBy periodPolynomial unipotentPart

namespace conclusion_resonance_z2_unipotent_complete_parity_data

/-- The mod-`2` parity shadow obtained by adding the nilpotent and unipotent pieces. -/
def paritySequence (D : conclusion_resonance_z2_unipotent_complete_parity_data) : ℕ → ZMod 2 :=
  fun n => D.nilpotentPart n + D.unipotentPart n

/-- The nilpotent piece is eventually periodic with the audited transient as a valid cutoff, the
unipotent tail admits the binomial-collapse description and the finite-field Jordan period bound,
and after the transient the full parity shadow agrees with the unipotent component alone. -/
def statement (D : conclusion_resonance_z2_unipotent_complete_parity_data) : Prop :=
  EventuallyPeriodic D.nilpotentPart (D.a_q * D.k) ∧
    (∃ c : Fin D.b_q → ZMod 2,
      (∀ n ≥ D.m0, D.unipotentPart n =
        ∑ j : Fin D.b_q, c j * (Nat.choose (n - D.m0) j : ZMod 2)) ∧
          ∃ T : ℕ, T ∣ 2 ^ D.b_q ∧ EventuallyPeriodic D.unipotentPart T) ∧
    (∃ T : ℕ,
      T ∣ periodBound 2 D.periodPolynomial ∧ EventuallyPeriodic D.unipotentPart T) ∧
    ∃ N : ℕ, ∀ n ≥ N, D.paritySequence n = D.unipotentPart n

end conclusion_resonance_z2_unipotent_complete_parity_data

/-- Paper label: `thm:conclusion-resonance-z2-unipotent-complete-parity`. Once the nilpotent
transient vanishes, the parity shadow is exactly the unipotent mod-`2` tail; that tail is
simultaneously governed by the binomial-collapse expansion and the finite-field Jordan period
bound. -/
theorem paper_conclusion_resonance_z2_unipotent_complete_parity
    (D : conclusion_resonance_z2_unipotent_complete_parity_data) : D.statement := by
  have hnil_periodic : EventuallyPeriodic D.nilpotentPart (D.a_q * D.k) := by
    refine ⟨D.a_q * D.k, ?_⟩
    intro n hn
    have hnow : D.nilpotentPart n = 0 := D.nilpotent_dies n hn
    have hshift : D.nilpotentPart (n + D.a_q * D.k) = 0 := by
      exact D.nilpotent_dies (n + D.a_q * D.k) (Nat.le_add_left _ _)
    simp [hnow, hshift]
  have hcollapse :=
    paper_conclusion_resonance_window_mod2_binomial_collapse
      0 D.b_q D.m0 D.unipotentPart D.unipotent_delta_nilpotent
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hjordan :=
    paper_conclusion_finitefield_jordan_exponent_period_bound
      2 D.unipotentPart D.periodPolynomial D.unipotent_eventually_annihilated
  refine ⟨hnil_periodic, ?_, ?_, ?_⟩
  · simpa using hcollapse
  · simpa using hjordan
  · refine ⟨D.a_q * D.k, ?_⟩
    intro n hn
    have hnil : D.nilpotentPart n = 0 := D.nilpotent_dies n hn
    simp [conclusion_resonance_z2_unipotent_complete_parity_data.paritySequence, hnil]

end Omega.Conclusion
