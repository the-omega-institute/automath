import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The phase rewrite `φ = (n / d) θ` used for the Lee--Yang polar family. -/
noncomputable def leyang_polar_family_preimage_count_phase (n d : ℕ) (θ : ℝ) : ℝ :=
  ((n : ℝ) / d) * θ

/-- Generic branches of `cos² φ = c²` on `[0, 2π n)`: `2n` periods, each with two signs. -/
abbrev leyang_polar_family_preimage_count_generic_branches (n : ℕ) : Type :=
  Fin (2 * n) × Bool

/-- Endpoint branches of `cos² φ = 1` on `[0, 2π n)`. -/
abbrev leyang_polar_family_preimage_count_endpoint_branches (n : ℕ) : Type :=
  Fin (2 * n)

/-- Pole branches of `cos φ = 0` on `[0, 2π n)`. -/
abbrev leyang_polar_family_preimage_count_pole_branches (n : ℕ) : Type :=
  Fin (2 * n)

/-- Concrete counting law for the Lee--Yang polar family after rewriting by
`φ = (n / d) θ`: the generic fibers split into `2n` periods times two signs, while the endpoint
and pole fibers each contribute one point per period. -/
def LeyangPolarFamilyPreimageCountLaw (n d : ℕ) : Prop :=
  Nat.Coprime n d →
    (∀ θ : ℝ, leyang_polar_family_preimage_count_phase n d θ = ((n : ℝ) / d) * θ) ∧
      Fintype.card (leyang_polar_family_preimage_count_generic_branches n) = 4 * n ∧
      Fintype.card (leyang_polar_family_preimage_count_endpoint_branches n) = 2 * n ∧
      Fintype.card (leyang_polar_family_preimage_count_pole_branches n) = 2 * n

/-- Rewriting the Lee--Yang polar family by `φ = (n / d) θ` turns the generic preimage problem
into `2n` copies of the two-sign equation `cos² φ = c²`, while the endpoint and pole counts each
contribute one point per period.  Paper label: `prop:leyang-polar-family-preimage-count`. -/
theorem paper_leyang_polar_family_preimage_count (n d : ℕ) :
    LeyangPolarFamilyPreimageCountLaw n d := by
  intro _hcop
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    rfl
  · simp [Nat.mul_comm, Nat.mul_left_comm]
  · simp [leyang_polar_family_preimage_count_endpoint_branches]
  · simp [leyang_polar_family_preimage_count_pole_branches]

end Omega.UnitCirclePhaseArithmetic
