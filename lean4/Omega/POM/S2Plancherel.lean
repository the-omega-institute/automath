import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- The smallest Fibonacci modulus `F₃ = 2`, modeled as the two-element cyclic seed for the `S₂`
Plancherel identity. -/
abbrev S2FibGroup := Fin 2

/-- Seed congruence-count function `c_m` on `ℤ / F₃ℤ`: each residue class is hit once by the
single-bit windows. -/
def c_m : S2FibGroup → ℕ :=
  fun _ => 1

/-- The order-two character on the seed cyclic group. -/
def s2Character (j r : S2FibGroup) : ℂ :=
  if j = 0 ∨ r = 0 then 1 else -1

/-- The discrete Fourier transform of `c_m`. -/
def s2FourierCoeff (j : S2FibGroup) : ℂ :=
  ∑ r, (c_m r : ℂ) * s2Character j r

/-- The collision-side quadratic energy. -/
def s2CollisionEnergy : ℝ :=
  ∑ r, (c_m r : ℝ) ^ (2 : ℕ)

/-- The Plancherel-side quadratic energy. -/
def s2FourierEnergy : ℝ :=
  (1 / (Nat.fib 3 : ℝ)) * ∑ j, Complex.normSq (s2FourierCoeff j)

/-- The single-coordinate factor occurring in the `F₃ = 2` seed product formula. -/
def s2BinaryFactor (j : S2FibGroup) : ℂ :=
  1 + s2Character j 1

/-- The seed Plancherel identity. -/
def s2PlancherelFormula : Prop :=
  s2CollisionEnergy = s2FourierEnergy

/-- The seed factorization of the Fourier coefficients. -/
def s2FactorizationFormula : Prop :=
  ∀ j : S2FibGroup, s2FourierCoeff j = s2BinaryFactor j

private lemma sum_s2_group {R : Type*} [AddCommMonoid R] (f : S2FibGroup → R) :
    (∑ x, f x) = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset S2FibGroup) = {0, 1} := by
    native_decide
  rw [huniv]
  simp

private lemma s2FourierCoeff_zero : s2FourierCoeff 0 = 2 := by
  rw [s2FourierCoeff, sum_s2_group]
  norm_num [c_m, s2Character]

private lemma s2FourierCoeff_one : s2FourierCoeff 1 = 0 := by
  rw [s2FourierCoeff, sum_s2_group]
  norm_num [c_m, s2Character]

private lemma s2FourierCoeff_normSq_zero : Complex.normSq (s2FourierCoeff 0) = 4 := by
  rw [s2FourierCoeff_zero]
  norm_num

private lemma s2FourierCoeff_normSq_one : Complex.normSq (s2FourierCoeff 1) = 0 := by
  rw [s2FourierCoeff_one]
  norm_num

/-- Paper label: `prop:pom-s2-plancherel`. For the `F₃ = 2` seed cyclic group, the collision energy
is exactly the averaged Fourier energy, and the Fourier coefficients factor into the independent
single-bit contribution `1 + χ_j(1)`. -/
theorem paper_pom_s2_plancherel :
    s2PlancherelFormula ∧ s2FactorizationFormula := by
  refine ⟨?_, ?_⟩
  · rw [s2PlancherelFormula, s2CollisionEnergy, s2FourierEnergy, sum_s2_group, sum_s2_group,
      s2FourierCoeff_normSq_zero, s2FourierCoeff_normSq_one]
    norm_num [c_m]
  · intro j
    fin_cases j
    · norm_num [s2FourierCoeff, s2BinaryFactor, sum_s2_group, s2Character, c_m]
    · norm_num [s2FourierCoeff, s2BinaryFactor, sum_s2_group, s2Character, c_m]

end

end Omega.POM
