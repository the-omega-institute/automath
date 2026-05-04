import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

lemma xi_smith_global_kernel_dmax_saturation_platform_top_le_of_value_eq_total {m : ℕ}
    (e : Fin m → ℕ) (k : ℕ) (h : smithPrefixValue e k = ∑ i, e i) :
    smithPrefixTop e ≤ k := by
  have hsum : (∑ i : Fin m, Nat.min (e i) k) = ∑ i : Fin m, e i := by
    simpa [smithPrefixValue] using h
  have hterm :
      ∀ i ∈ (Finset.univ : Finset (Fin m)), Nat.min (e i) k = e i := by
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => Nat.min_le_left (e i) k)).mp hsum
  unfold smithPrefixTop
  refine Finset.sup_le ?_
  intro i hi
  exact min_eq_left_iff.mp (hterm i hi)

/-- Paper label: `thm:xi-smith-global-kernel-dmax-saturation-platform`. -/
theorem paper_xi_smith_global_kernel_dmax_saturation_platform {ι : Type*} [Fintype ι]
    {m : ℕ} (e : ι → Fin m → ℕ) (ν : ι → ℕ) :
    ((∀ p, Omega.Zeta.smithPrefixTop (e p) ≤ ν p) ↔
      (∀ p, Omega.Zeta.smithPrefixValue (e p) (ν p) = ∑ i, e p i)) := by
  constructor
  · intro h p
    exact smithPrefixValue_eq_total_of_le_top (e p) (ν p) (h p)
  · intro h p
    exact xi_smith_global_kernel_dmax_saturation_platform_top_le_of_value_eq_total
      (e p) (ν p) (h p)

end Omega.Zeta
