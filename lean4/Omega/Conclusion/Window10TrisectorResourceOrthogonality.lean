import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibonacciAnomalyBlock
import Omega.Folding.ZeckendorfSignature
import Omega.Zeta.Window6RenyiDivergenceParityChargeRedundancy

namespace Omega.Conclusion

/-- Completion-sector witness for the audited window-`10` package. -/
def derivedWindow10CompletionWitness : ℕ := Nat.fib 10

/-- Parity-sector witness for the audited window-`10` package. -/
def derivedWindow10ParityWitness : ℕ := Nat.fib 9 + Nat.fib 7 + Nat.fib 5

/-- Entropy-sector witness for the audited window-`10` package. -/
noncomputable def derivedWindow10EntropyWitness : ℝ := Omega.Zeta.window6ShannonEntropy

/-- The completion axis is dominated by the `55`-sector and strictly exceeds the parity witness. -/
def derivedWindow10CompletionAxisDominated : Prop :=
  derivedWindow10CompletionWitness = 55 ∧
    derivedWindow10ParityWitness < derivedWindow10CompletionWitness

/-- The parity axis is controlled by the audited `52`-sector and exceeds the entropy rank `37`. -/
def derivedWindow10ParityAxisDominated : Prop :=
  derivedWindow10ParityWitness = 52 ∧ 37 < derivedWindow10ParityWitness

/-- The entropy axis is governed by the `37`-sector formula and stays below its `log 2` envelope. -/
def derivedWindow10EntropyAxisDominated : Prop :=
  derivedWindow10EntropyWitness =
      (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3 ∧
    derivedWindow10EntropyWitness < (37 / 8 : ℝ) * Real.log 2

/-- The audited window-`10` package is orthogonal across its completion (`55`), parity (`52`), and
entropy (`37`) sectors.
    thm:derived-window10-trisector-resource-orthogonality -/
theorem paper_derived_window10_trisector_resource_orthogonality :
    derivedWindow10CompletionAxisDominated ∧
      derivedWindow10ParityAxisDominated ∧
      derivedWindow10EntropyAxisDominated := by
  have hcompletion : derivedWindow10CompletionWitness = 55 := by
    simpa [derivedWindow10CompletionWitness] using Omega.Conclusion.FibonacciAnomalyBlock.fib_ten_eq
  have hparity : derivedWindow10ParityWitness = 52 := by
    simpa [derivedWindow10ParityWitness] using Omega.ZeckSig.dim_F4.symm
  have hentropy :=
    Omega.Zeta.paper_xi_window6_renyi_divergence_parity_charge_redundancy
  rcases hentropy with ⟨_, hshannon, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hcompletion, ?_⟩
    omega
  · refine ⟨hparity, ?_⟩
    omega
  · refine ⟨?_, ?_⟩
    · simpa [derivedWindow10EntropyWitness] using hshannon
    · rw [derivedWindow10EntropyWitness, hshannon]
      have hlog3 : 0 < Real.log 3 := by
        have hthree : (1 : ℝ) < 3 := by norm_num
        simpa using Real.log_pos hthree
      linarith

end Omega.Conclusion
