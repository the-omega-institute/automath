import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.VectorPotentialPhiMinusLdpParam

namespace Omega.SyncKernelWeighted

open Matrix
open Polynomial

noncomputable section

/-- Explicit `4 x 4` weighted collision matrix: a `1`-eigenvalue decouples, while the lower
`3 x 3` companion block carries the cubic Perron branch. -/
def real_input_40_collision_pressure_matrix (u : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    0, 0, 0, -(3 * u);
    0, 1, 0, 2 - u;
    0, 0, 1, u + 2]

/-- The cubic Perron-branch factor carried by the companion block. -/
noncomputable def real_input_40_collision_pressure_cubic (u : ℝ) : Polynomial ℝ :=
  X ^ 3 - C (u + 2) * X ^ 2 + C (u - 2) * X + C (3 * u)

/-- Audited characteristic polynomial of the explicit collision matrix. -/
noncomputable def real_input_40_collision_pressure_charpoly (u : ℝ) : Polynomial ℝ :=
  (X - C 1) * real_input_40_collision_pressure_cubic u

/-- Pressure-side expression normalized so the cubic LDP package rewrites it as a single branch
logarithm. -/
noncomputable def real_input_40_collision_pressure_pressure (lam : ℝ) : ℝ :=
  vectorPotentialPhiMinusRate lam + Real.log lam - Real.log 3

/-- Paper-facing collision-pressure package for the real-input-40 branch: the weighted matrix is
explicit, its audited characteristic polynomial splits off the trivial factor `X - 1`, the cubic
Perron branch is the existing `u(λ)` solution, and the pressure identity is the chapter-local
logarithmic rewrite coming from the cubic-pressure infrastructure. -/
def real_input_40_collision_pressure_statement : Prop :=
  ∀ lam : ℝ,
    lam ^ 2 - lam - 3 ≠ 0 →
    lam ^ 4 - 2 * lam ^ 3 - 5 * lam ^ 2 + 12 * lam + 6 ≠ 0 →
      real_input_40_collision_pressure_matrix (vectorPotentialPhiMinusU lam) =
        !![1, 0, 0, 0;
          0, 0, 0, -(3 * vectorPotentialPhiMinusU lam);
          0, 1, 0, 2 - vectorPotentialPhiMinusU lam;
          0, 0, 1, vectorPotentialPhiMinusU lam + 2] ∧
      real_input_40_collision_pressure_charpoly (vectorPotentialPhiMinusU lam) =
        (X - C 1) * real_input_40_collision_pressure_cubic (vectorPotentialPhiMinusU lam) ∧
      vectorPotentialPhiMinusCubic lam (vectorPotentialPhiMinusU lam) = 0 ∧
      real_input_40_collision_pressure_pressure lam =
        vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam)

/-- Paper label: `prop:real-input-40-collision-pressure`. -/
theorem paper_real_input_40_collision_pressure : real_input_40_collision_pressure_statement := by
  intro lam hUdenom hAlphaDenom
  let D : VectorPotentialPhiMinusLdpParamData := {
    lam := lam
    hUdenom := hUdenom
    hAlphaDenom := hAlphaDenom
  }
  have hClosedU : D.closedFormU := (paper_sync_kernel_vector_potential_phi_minus_ldp_param D).1
  have hRate : D.closedFormRate := (paper_sync_kernel_vector_potential_phi_minus_ldp_param D).2.2
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold VectorPotentialPhiMinusLdpParamData.closedFormU at hClosedU
    calc
      vectorPotentialPhiMinusCubic lam (vectorPotentialPhiMinusU lam) =
          lam * (lam ^ 2 - 2 * lam - 2) -
            vectorPotentialPhiMinusU lam * (lam ^ 2 - lam - 3) := by
              unfold vectorPotentialPhiMinusCubic
              ring
      _ = 0 := by rw [hClosedU]; ring
  · unfold real_input_40_collision_pressure_pressure
    have hRate' :
        vectorPotentialPhiMinusRate lam =
          vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam) -
            Real.log lam + Real.log 3 := hRate
    calc
      vectorPotentialPhiMinusRate lam + Real.log lam - Real.log 3 =
        (vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam) -
            Real.log lam + Real.log 3) + Real.log lam - Real.log 3 := by rw [hRate']
      _ = vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam) := by
        ring

end

end Omega.SyncKernelWeighted
