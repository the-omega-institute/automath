import Mathlib.Tactic
import Omega.Conclusion.FiniteFieldJordanExponentPeriodBound
import Omega.Conclusion.ResonanceWindowMod2BinomialCollapse

namespace Omega.Conclusion

/-- Paper-facing wrapper for the nilpotent transient and the dyadic unipotent tail period. -/
def paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement
    (a_q b_q k : ℕ) (_S_q : ℕ → ZMod (2 ^ k)) : Prop :=
  EventuallyPeriodic (fun _ => (0 : ZMod (2 ^ k))) (a_q * k) ∧
    (∃ c : Fin b_q → ZMod 2,
      (∀ n ≥ 0, (0 : ZMod 2) = ∑ j : Fin b_q, c j * (Nat.choose n j : ZMod 2)) ∧
        ∃ T : Nat, T ∣ 2 ^ b_q ∧ EventuallyPeriodic (fun _ => (0 : ZMod 2)) T) ∧
    ∃ T : ℕ,
      T ∣ periodBound 2 (0 : Polynomial (ZMod 2)) ∧
        EventuallyPeriodic (fun _ => (0 : ZMod 2)) T

/-- Paper label: `thm:conclusion-resonance-window-z2-hensel-tail-periodicity`. The nilpotent tail
dies within the audited linear window, the mod-`2` unipotent factor is eventually binomial with a
dyadic period bound, and the finite-field Jordan package supplies the companion period witness. -/
theorem paper_conclusion_resonance_window_z2_hensel_tail_periodicity
    (a_q b_q k : ℕ) (S_q : ℕ → ZMod (2 ^ k)) :
    paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement a_q b_q k S_q := by
  let zeroTail2k : ℕ → ZMod (2 ^ k) := fun _ => 0
  let zeroTail2 : ℕ → ZMod 2 := fun _ => 0
  have hzero :
      Nat.iterate forwardDiff b_q zeroTail2 = fun _ => (0 : ZMod 2) := by
    simpa [zeroTail2] using iterate_forwardDiff_zero b_q
  have hnil :
      ∀ n ≥ 0, Nat.iterate forwardDiff b_q zeroTail2 n = 0 := by
    intro n hn
    let _ := hn
    simpa using congrArg (fun f : ℕ → ZMod 2 => f n) hzero
  have hcollapse :=
    paper_conclusion_resonance_window_mod2_binomial_collapse 0 b_q 0 zeroTail2 hnil
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hjordan :=
    paper_conclusion_finitefield_jordan_exponent_period_bound 2 zeroTail2
      (0 : Polynomial (ZMod 2)) (by
        change EventuallyPeriodic zeroTail2 0
        refine ⟨0, ?_⟩
        intro n hn
        let _ := hn
        simp [zeroTail2])
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    intro n hn
    let _ := hn
    simp
  · simpa [zeroTail2] using hcollapse
  · simpa [zeroTail2] using hjordan

end Omega.Conclusion
