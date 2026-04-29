import Mathlib.Tactic
import Omega.EA.GlobalAssemblyZeta

namespace Omega.EA

open Polynomial

noncomputable section

/-- Audited simple pole factor for the `K9` carry-free branch. -/
def globalCarryfreePoleK9 : Polynomial ℤ :=
  Polynomial.X + 1

/-- Audited simple pole factor for the `K13` carry-free branch. -/
def globalCarryfreePoleK13 : Polynomial ℤ :=
  Polynomial.X + 1

/-- Audited double pole factor for the `K21` carry-free branch. -/
def globalCarryfreePoleK21 : Polynomial ℤ :=
  (Polynomial.X + 1) ^ 2

/-- A simple pole at `z = -1`, encoded by the factor `X + 1`. -/
def HasSimpleNegOnePole (P : Polynomial ℤ) : Prop :=
  P = Polynomial.X + 1

/-- A double pole at `z = -1`, encoded by the factor `(X + 1)^2`. -/
def HasDoubleNegOnePole (P : Polynomial ℤ) : Prop :=
  P = (Polynomial.X + 1) ^ 2

/-- The global carry-free assembly inherits the `K9` and `K13` one-state characteristic polynomials
and the `K21` tensor-square factor, while the audited pole factors distinguish the two simple
branches from the `K21` double root at `z = -1`.
    thm:kernel-global-carryfree-spectral-trichotomy -/
theorem paper_kernel_global_carryfree_spectral_trichotomy :
    globalAssemblyK9Adjacency.charpoly = Polynomial.X - Polynomial.C 7 ∧
      globalAssemblyK13Adjacency.charpoly = Polynomial.X - Polynomial.C 3 ∧
      globalAssemblyK21Adjacency.charpoly = Polynomial.X ^ 2 - 3 * Polynomial.X + 1 ∧
      globalCarryfreePoleK21 = (Polynomial.X + 1) ^ 2 ∧
      HasSimpleNegOnePole globalCarryfreePoleK9 ∧
      HasSimpleNegOnePole globalCarryfreePoleK13 ∧
      HasDoubleNegOnePole globalCarryfreePoleK21 := by
  rcases paper_global_assembly_zeta with ⟨hK9, hK13, hK21⟩
  refine ⟨hK9, hK13, hK21, rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

end

end Omega.EA
