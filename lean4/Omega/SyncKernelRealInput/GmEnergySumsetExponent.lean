import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped Combinatorics.Additive Pointwise

/-- The representation count of a sum `s` by ordered pairs from `A`. -/
def gm_energy_sumset_exponent_representation_count (A : Finset ℤ) (s : ℤ) : ℕ :=
  ((A ×ˢ A).filter fun xy => xy.1 + xy.2 = s).card

/-- Paper label: `prop:gm-energy-sumset-exponent`. The ordered-pair representation count on
`A + A` sums to `|A|²`, its square-sum is exactly the additive energy, and Cauchy-Schwarz yields
the standard lower bound `|A|⁴ ≤ |A + A| E(A)` in the self-sum case. -/
def gm_energy_sumset_exponent_statement (A : Finset ℤ) : Prop :=
  (∑ s ∈ A + A, gm_energy_sumset_exponent_representation_count A s = A.card ^ 2) ∧
    Finset.addEnergy A A = ∑ s ∈ A + A, gm_energy_sumset_exponent_representation_count A s ^ 2 ∧
    A.card ^ 2 * A.card ^ 2 ≤ (A + A).card * Finset.addEnergy A A

theorem paper_gm_energy_sumset_exponent (A : Finset ℤ) :
    gm_energy_sumset_exponent_statement A := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ∑ s ∈ A + A, gm_energy_sumset_exponent_representation_count A s
        = ((A ×ˢ A).filter fun xy => xy.1 + xy.2 ∈ A + A).card := by
            simpa [gm_energy_sumset_exponent_representation_count] using
              (Finset.sum_card_fiberwise_eq_card_filter (s := A ×ˢ A) (t := A + A)
                (g := fun xy : ℤ × ℤ => xy.1 + xy.2))
      _ = A.card ^ 2 := by
            have hfilter :
                (A ×ˢ A).filter (fun xy : ℤ × ℤ => xy.1 + xy.2 ∈ A + A) = A ×ˢ A := by
              ext xy
              simp only [Finset.mem_filter, Finset.mem_product]
              constructor
              · intro hxy
                exact hxy.1
              · intro hxy
                exact ⟨hxy, Finset.mem_add.2 ⟨xy.1, hxy.1, xy.2, hxy.2, rfl⟩⟩
            rw [hfilter, Finset.card_product, pow_two]
  · simpa [gm_energy_sumset_exponent_representation_count] using Finset.addEnergy_eq_sum_sq' A A
  · simpa using Finset.le_card_add_mul_addEnergy A A

end Omega.SyncKernelRealInput
