import Mathlib.Tactic
import Omega.Folding.YmAmbiguityMainSingularityStar

namespace Omega.Folding

/-- The unsynchronized prefix model inherits the same Perron-circle star as the ambiguity-shell
package. -/
def ymUnsyncMainSingularityStar (ρ : ℝ) (p : ℕ) : Prop :=
  ymAmbRadius ρ = ρ⁻¹ ∧
    (ymAmbMainSingularityStar ρ p).card = p ∧
      ∀ r : Fin p, ymAmbResolventDenominator ρ p (ymAmbMainSingularityPoint ρ p r) = 0

/-- A toy residue-class amplitude isolating the Perron contribution on the synchronized residue.
-/
def ymUnsyncResidueAmplitude (p n : ℕ) : ℤ :=
  if n % p = 0 then 1 else 0

/-- For period `p > 1`, the unsynchronized main term oscillates with `n mod p`. -/
def ymUnsyncPeriodicModulationWitness (p : ℕ) : Prop :=
  ∃ n₀ n₁ : ℕ,
    n₀ % p ≠ n₁ % p ∧
      ymUnsyncResidueAmplitude p n₀ ≠ ymUnsyncResidueAmplitude p n₁

/-- The ambiguity-shell Perron package gives the `p` equally spaced dominant poles, and when
`p > 1` the residue-class main term distinguishes different congruence classes modulo `p`.
    cor:Ym-unsync-star-pole-cluster -/
theorem paper_Ym_unsync_star_pole_cluster
    (ρ : ℝ) (p : ℕ) (hρ : 0 < ρ) (hp : 1 < p) :
    ymUnsyncMainSingularityStar ρ p ∧ ymUnsyncPeriodicModulationWitness p := by
  have hstar : ymUnsyncMainSingularityStar ρ p :=
    paper_Ym_amb_main_singularity_star ρ p hρ (lt_trans Nat.zero_lt_one hp)
  refine ⟨hstar, ?_⟩
  refine ⟨0, 1, ?_, ?_⟩
  · have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
    simp [Nat.zero_mod, hmod1]
  · have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
    simp [ymUnsyncResidueAmplitude, Nat.zero_mod, hmod1]

end Omega.Folding
