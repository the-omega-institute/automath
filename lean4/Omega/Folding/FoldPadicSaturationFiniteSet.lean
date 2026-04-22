import Omega.Folding.FoldPadicSaturationPrime

namespace Omega.Folding

/-- Common finite-union failure bound obtained by reusing one linear `p`-adic saturation scale for
every prime in a finite family. -/
def foldPadicFiniteSetFailureBound (S : Finset ℕ) (z : ℕ) (a : ZMod z) (μ c : ℝ) : Prop :=
  ∀ m : ℕ,
    2 * z ≤ m →
      (S.card : ℝ) * componentResidueLowerTailProb z a m μ ≤
        (S.card : ℝ) * Real.exp (-c * m)

/-- Paper-facing finite-set version of the prime-direction saturation statement: each prime in the
finite family inherits the linear saturation package, and a single pair of positive constants gives
the union-bound exponential tail rate. -/
def foldPadicSaturationFiniteSetStatement : Prop :=
  ∀ (S : Finset ℕ) (z : ℕ) (a : ZMod z),
    2 ≤ z →
    (∀ p ∈ S, Nat.Prime p) →
    (∀ p ∈ S, foldPrimeEntryPointDivisibility p z) →
      ∃ μ c : ℝ,
        0 < μ ∧
          0 < c ∧
          (∀ p ∈ S, foldPrimeEntryPointDivisibility p z ∧ foldLinearPadicSaturation z a) ∧
          foldPadicFiniteSetFailureBound S z a μ c

theorem paper_fold_padic_saturation_finite_set : foldPadicSaturationFiniteSetStatement := by
  intro S z a hz hprime hentry
  rcases paper_fold_component_residue_pressure_ld z a hz with
    ⟨μ, c, hμ, hc, _hμeq, _hceq, _hmgf, _hmean, htail⟩
  refine ⟨μ, c, hμ, hc, ?_, ?_⟩
  · intro p hp
    exact paper_fold_padic_saturation_prime p z a (hprime p hp) hz (hentry p hp)
  · intro m hm
    exact mul_le_mul_of_nonneg_left (htail m hm) (by positivity)

end Omega.Folding
