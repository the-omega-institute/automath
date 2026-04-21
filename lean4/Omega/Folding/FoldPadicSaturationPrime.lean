import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.ComponentResiduePressurePadicSaturation

namespace Omega.Folding

/-- Divisibility criterion attached to a chosen Fibonacci entry point `z = Z(p)`. -/
def foldPrimeEntryPointDivisibility (p z : ℕ) : Prop :=
  ∀ n : ℕ, p ∣ Nat.fib n ↔ z ∣ n

/-- Linear `p`-adic saturation package extracted from the explicit residue-pressure model. -/
def foldLinearPadicSaturation (z : ℕ) (a : ZMod z) : Prop :=
  ∃ mu c : ℝ,
    0 < mu ∧
      0 < c ∧
      mu = 1 / (2 * z) ∧
      c = 1 ∧
      (∀ θ : ℝ,
        componentResidueLogMgfLimit z a θ =
          Real.log (componentResiduePerronRoot z θ) -
            Real.log (componentResiduePerronRoot z 0)) ∧
      componentResidueMean z a = 1 / z ∧
      (∀ m : ℕ, 2 * z ≤ m →
        componentResidueLowerTailProb z a m mu ≤ Real.exp (-c * m))

/-- Paper-facing prime-direction `p`-adic saturation: once the Fibonacci entry-point divisibility
criterion is fixed, the cyclic residue-pressure model yields a linear lower-tail bound along that
residue class.
    cor:fold-padic-saturation-prime -/
def paper_fold_padic_saturation_prime_statement : Prop :=
  ∀ (p z : ℕ) (a : ZMod z),
    Nat.Prime p →
    2 ≤ z →
    foldPrimeEntryPointDivisibility p z →
      foldPrimeEntryPointDivisibility p z ∧ foldLinearPadicSaturation z a

theorem paper_fold_padic_saturation_prime : paper_fold_padic_saturation_prime_statement := by
  intro p z a hp hz hEntry
  rcases paper_fold_component_residue_pressure_ld z a hz with
    ⟨mu, c, hmu, hc, hmu_eq, hc_eq, hMgf, hMean, hTail⟩
  exact ⟨hEntry, ⟨mu, c, hmu, hc, hmu_eq, hc_eq, hMgf, hMean, hTail⟩⟩

end Omega.Folding
