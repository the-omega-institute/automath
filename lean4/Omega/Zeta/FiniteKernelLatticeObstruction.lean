import Mathlib.Tactic

namespace Omega.Zeta

/-- A toy finite kernel model remembers how many vertical pole families appear and how many
zeroes/poles lie below a height cutoff. -/
structure FiniteKernel where
  poleFamilies : ℕ
  poleCount : ℕ → ℕ

/-- Every nonzero eigenvalue contributes one vertical arithmetic pole progression. -/
def verticalArithmeticPoleLattice (K : FiniteKernel) : Prop :=
  0 < K.poleFamilies

/-- Finite products and quotients of such factors have at most linear zero/pole growth. -/
def linearPoleCount (K : FiniteKernel) : Prop :=
  ∀ T : ℕ, K.poleCount T ≤ K.poleFamilies * (T + 1)

/-- A toy superlinear stand-in for Riemann-von-Mangoldt growth. -/
def riemannVonMangoldtToy (T : ℕ) : ℕ :=
  T * (T + 2)

/-- The linear pole bound must eventually fall short of the toy Riemann-von-Mangoldt growth. -/
def noRiemannVonMangoldtMatch (K : FiniteKernel) : Prop :=
  ∃ T : ℕ, K.poleCount T < riemannVonMangoldtToy T

/-- Vertical arithmetic progressions give only linear pole counts, which cannot match the
superlinear toy Riemann-von-Mangoldt profile.
    prop:finite-kernel-lattice-obstruction -/
theorem paper_finite_kernel_lattice_obstruction {K : FiniteKernel} :
    verticalArithmeticPoleLattice K -> linearPoleCount K -> noRiemannVonMangoldtMatch K := by
  intro hLattice hLinear
  refine ⟨K.poleFamilies, ?_⟩
  have hFamiliesPos : 0 < K.poleFamilies := hLattice
  calc
    K.poleCount K.poleFamilies ≤ K.poleFamilies * (K.poleFamilies + 1) := by
      simpa using hLinear K.poleFamilies
    _ < K.poleFamilies * (K.poleFamilies + 2) := by
      have hlt : K.poleFamilies + 1 < K.poleFamilies + 2 := by omega
      exact Nat.mul_lt_mul_of_pos_left hlt hFamiliesPos
    _ = riemannVonMangoldtToy K.poleFamilies := by
      simp [riemannVonMangoldtToy]

end Omega.Zeta
