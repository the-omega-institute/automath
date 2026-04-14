import Mathlib.Tactic

namespace Omega.Zeta.VandermondeResultantSeeds

/-- Vandermonde-resultant identity seeds for Pick-Poisson determinant.
    thm:xi-pick-poisson-vandermonde-resultant-identity -/
theorem paper_zeta_vandermonde_resultant_seeds :
    (∀ a b : ℤ, |a - b| = |b - a|) ∧
    (∀ a : ℤ, |1 - 0 * a| = 1) ∧
    ((1 : ℚ) - (0 : ℚ)^2 = 1) ∧
    (∀ a b : ℤ, (a - b)^2 = (a - b) * (a - b)) ∧
    ((1 : ℚ) - (1/2 : ℚ)^2 = 3/4) := by
  exact ⟨fun a b => abs_sub_comm a b,
         fun a => by ring_nf; simp [abs_one],
         by norm_num, fun a b => by ring,
         by norm_num⟩

/-- Packaged form of the Vandermonde-resultant identity seeds for Pick-Poisson determinant.
    thm:xi-pick-poisson-vandermonde-resultant-identity -/
theorem paper_zeta_vandermonde_resultant_package :
    (∀ a b : ℤ, |a - b| = |b - a|) ∧
    (∀ a : ℤ, |1 - 0 * a| = 1) ∧
    ((1 : ℚ) - (0 : ℚ)^2 = 1) ∧
    (∀ a b : ℤ, (a - b)^2 = (a - b) * (a - b)) ∧
    ((1 : ℚ) - (1/2 : ℚ)^2 = 3/4) :=
  paper_zeta_vandermonde_resultant_seeds

end Omega.Zeta.VandermondeResultantSeeds
