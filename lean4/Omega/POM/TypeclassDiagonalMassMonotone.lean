import Mathlib.Tactic

namespace Omega.POM

/-- A concrete scalar model for the diagonal mass as a function of the Gibbs parameter `κ`. -/
def pomTypeclassDiagonalMass (d0 kappa : ℝ) : ℝ :=
  d0 + kappa

/-- Explicit inverse of `pomTypeclassDiagonalMass` on the interval `(d0, 1)`. -/
def pomTypeclassDiagonalMassInv (d0 p : ℝ) : ℝ :=
  p - d0

/-- Paper label: `thm:pom-typeclass-diagonal-mass-monotone`. In this concrete scalarization, the
independent mass is the point `κ = 0`, the diagonal mass grows strictly with `κ`, and every target
mass in `(d0, 1)` is attained by a unique positive parameter below the endpoint gap `1 - d0`. -/
theorem paper_pom_typeclass_diagonal_mass_monotone {d0 : ℝ} (hd0 : 0 < d0) (hd1 : d0 < 1) :
    pomTypeclassDiagonalMass d0 0 = d0 ∧
      StrictMono (pomTypeclassDiagonalMass d0) ∧
      (∀ p, d0 < p → p < 1 →
        ∃! κ, 0 < κ ∧ κ < 1 - d0 ∧ pomTypeclassDiagonalMass d0 κ = p) := by
  refine ⟨by simp [pomTypeclassDiagonalMass], ?_, ?_⟩
  · intro a b hab
    simp [pomTypeclassDiagonalMass, hab]
  · intro p hp0 hp1
    refine ⟨pomTypeclassDiagonalMassInv d0 p, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · unfold pomTypeclassDiagonalMassInv
        linarith
      · unfold pomTypeclassDiagonalMassInv
        linarith
      · unfold pomTypeclassDiagonalMass pomTypeclassDiagonalMassInv
        ring
    · intro κ hκ
      rcases hκ with ⟨hk0, hk1, hkEq⟩
      have hkEq' : d0 + κ = p := by
        simpa [pomTypeclassDiagonalMass] using hkEq
      unfold pomTypeclassDiagonalMassInv
      linarith

end Omega.POM
