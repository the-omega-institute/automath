import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
import Omega.Conclusion.ZeckendorfEulerReindexing

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-zeckendorf-euler-superexponential-tail`. Reindexing the
Zeckendorf factorial sum leaves the omitted factorial tail, whose total mass is bounded by the
first omitted term times a geometric series. This packages the exact reindexing step together with
the concrete factorial-tail upper bound used in the paper's superexponential-decay argument. -/
theorem paper_conclusion_zeckendorf_euler_superexponential_tail (m : ℕ) :
    let N := Nat.fib (m + 2)
    let tail : ℝ := ∑' k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹
    (∑ x : Omega.X m, ((Nat.factorial (Omega.stableValue x) : ℕ) : ℝ)⁻¹) =
        ∑ i : Fin N, ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹ ∧
      0 < tail ∧
      tail ≤ 2 / (Nat.factorial N : ℝ) := by
  dsimp
  let N := Nat.fib (m + 2)
  have hreindex := paper_conclusion_zeckendorf_euler_reindexing m
  have hNpos_nat : 0 < N := by
    simpa [N] using Nat.fib_pos.2 (Nat.succ_pos (m + 1))
  have hfac_pos : 0 < (Nat.factorial N : ℝ) := by positivity
  have hpow_fac : ∀ k : ℕ, N.factorial * 2 ^ k ≤ (N + k).factorial := by
    intro k
    have htwo_le : 2 ≤ N + 1 := by omega
    have hpow : 2 ^ k ≤ (N + 1) ^ k := by
      exact Nat.pow_le_pow_left htwo_le k
    exact le_trans (Nat.mul_le_mul_left _ hpow) Nat.factorial_mul_pow_le_factorial
  have hterm_bound :
      ∀ k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹ ≤
        (Nat.factorial N : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ k) := by
    intro k
    have hpow_fac_real : ((N.factorial * 2 ^ k : ℕ) : ℝ) ≤ (N + k).factorial := by
      exact_mod_cast hpow_fac k
    have hleft_pos : 0 < (((N.factorial * 2 ^ k : ℕ) : ℝ)) := by positivity
    have hright_pos : 0 < ((Nat.factorial (N + k) : ℕ) : ℝ) := by positivity
    have hinv :
        ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹ ≤ (((N.factorial * 2 ^ k : ℕ) : ℝ))⁻¹ := by
      exact (inv_le_inv₀ hright_pos hleft_pos).2 hpow_fac_real
    calc
      ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹ ≤ (((N.factorial * 2 ^ k : ℕ) : ℝ))⁻¹ := hinv
      _ = (Nat.factorial N : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ k) := by
            have hpow_half : ((((2 : ℕ) : ℝ) ^ k)⁻¹) = ((1 / 2 : ℝ) ^ k) := by
              rw [one_div, inv_pow]
              norm_num
            rw [Nat.cast_mul, Nat.cast_pow, mul_inv_rev, hpow_half]
            ring
  have hsummable_geom : Summable (fun k : ℕ => (Nat.factorial N : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ k)) := by
    exact Summable.mul_left _ summable_geometric_two
  have hsummable_tail : Summable (fun k : ℕ => ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹) := by
    exact Summable.of_nonneg_of_le (fun _ => by positivity) hterm_bound hsummable_geom
  have htail_le_geom :
      (∑' k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹) ≤
        ∑' k : ℕ, (Nat.factorial N : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ k) := by
    exact hsummable_tail.tsum_le_tsum hterm_bound hsummable_geom
  have htail_bound :
      (∑' k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹) ≤ 2 / (Nat.factorial N : ℝ) := by
    calc
      (∑' k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹) ≤
          ∑' k : ℕ, (Nat.factorial N : ℝ)⁻¹ * ((1 / 2 : ℝ) ^ k) := by
            exact htail_le_geom
      _ = (Nat.factorial N : ℝ)⁻¹ * 2 := by
            rw [tsum_mul_left, tsum_geometric_two]
      _ = 2 / (Nat.factorial N : ℝ) := by
            field_simp [hfac_pos.ne']
  have htail_pos :
      0 < ∑' k : ℕ, ((Nat.factorial (N + k) : ℕ) : ℝ)⁻¹ := by
    refine hsummable_tail.tsum_pos ?_ 0 ?_
    · intro k
      positivity
    · positivity
  exact ⟨by simpa [N] using hreindex, htail_pos, htail_bound⟩

end Omega.Conclusion
