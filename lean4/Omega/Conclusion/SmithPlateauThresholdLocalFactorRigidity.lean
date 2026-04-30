import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete Smith p-kernel profile data for the plateau threshold rigidity statement. -/
structure conclusion_smith_plateau_threshold_local_factor_rigidity_data where
  width : ℕ
  exponents : Fin width → ℕ

/-- The exact prefix package: finite differences recover exponent multiplicities, the first
plateau occurs at `E + 1`, and the singleton profiles `E` and `E + 1` are the uniform shorter
prefix ambiguity. -/
def conclusion_smith_plateau_threshold_local_factor_rigidity_data.statement
    (D : conclusion_smith_plateau_threshold_local_factor_rigidity_data) : Prop :=
  let E := smithPrefixTop D.exponents
  (∀ k : ℕ, 1 ≤ k → k ≤ E →
      smithPrefixValue D.exponents (k - 1) < smithPrefixValue D.exponents k) ∧
    smithPrefixValue D.exponents (E + 1) = smithPrefixValue D.exponents E ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
      smithPrefixMultiplicity D.exponents ℓ =
        2 * smithPrefixValue D.exponents ℓ -
          smithPrefixValue D.exponents (ℓ - 1) -
            smithPrefixValue D.exponents (ℓ + 1)) ∧
    (1 ≤ E →
      smithPrefixMultiplicity D.exponents E =
        smithPrefixValue D.exponents E - smithPrefixValue D.exponents (E - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      smithPrefixValue (fun _ : Fin 1 => E) k =
        smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1) ∧
    (∀ k : ℕ,
      smithPrefixValue D.exponents k = ∑ i : Fin D.width, Nat.min (D.exponents i) k) ∧
    (∀ k : ℕ, E ≤ k →
      smithPrefixValue D.exponents k = smithPrefixValue D.exponents E)

/-- Paper label: `thm:conclusion-smith-plateau-threshold-local-factor-rigidity`.  The local
Smith profile is exactly the prefix sum of `min k e_i`; its finite differences recover the
multiplicities, and the first plateau value is both sufficient and uniformly necessary. -/
theorem paper_conclusion_smith_plateau_threshold_local_factor_rigidity
    (D : conclusion_smith_plateau_threshold_local_factor_rigidity_data) : D.statement := by
  let E := smithPrefixTop D.exponents
  have hbase :
      (∀ k : ℕ, 1 ≤ k → k ≤ E →
          smithPrefixValue D.exponents (k - 1) < smithPrefixValue D.exponents k) ∧
        smithPrefixValue D.exponents (E + 1) = smithPrefixValue D.exponents E ∧
        (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
          smithPrefixMultiplicity D.exponents ℓ =
            2 * smithPrefixValue D.exponents ℓ -
              smithPrefixValue D.exponents (ℓ - 1) -
                smithPrefixValue D.exponents (ℓ + 1)) ∧
        (1 ≤ E →
          smithPrefixMultiplicity D.exponents E =
            smithPrefixValue D.exponents E - smithPrefixValue D.exponents (E - 1)) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ E →
          smithPrefixValue (fun _ : Fin 1 => E) k =
            smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
        smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
          smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1) := by
    simpa [E] using paper_xi_smith_p_kernel_shortest_sufficient_prefix D.exponents
  rcases hbase with ⟨hstrict, hplateau, hmultiplicity, hterminal, hambiguity, hdetect⟩
  refine
    ⟨hstrict, hplateau, hmultiplicity, hterminal, hambiguity, hdetect, ?_, ?_⟩
  · intro k
    rfl
  · intro k hk
    rw [smithPrefixValue_eq_total_of_le_top D.exponents k hk,
      smithPrefixValue_eq_total_of_le_top D.exponents E le_rfl]

end Omega.Conclusion
