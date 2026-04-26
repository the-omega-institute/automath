import Omega.SyncKernelRealInput.CoreThermodynamicTailEquivalence
import Omega.SyncKernelRealInput.InputMeasureRigid
import Omega.SyncKernelWeighted.RealInput40CollisionPressure

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted
open Matrix Polynomial

/-- Paper label: `cor:real-input-40-input-potential-reduction`. The input-measure rigidity
package identifies the input-only pushforward with the explicit product law on the four memory
states, while the thermodynamic and collision-pressure packages reduce the pressure data to the
audited `4 × 4` weighted adjacency matrix. -/
theorem paper_real_input_40_input_potential_reduction
    (c θ0 lam : ℝ) (hc : 1 < c)
    (hUdenom : lam ^ 2 - lam - 3 ≠ 0)
    (hAlphaDenom : lam ^ 4 - 2 * lam ^ 3 - 5 * lam ^ 2 + 12 * lam + 6 ≠ 0) :
    RealInput40ResetWordStatement ∧
      RealInput40InputMemoryMarginalClosedForm ∧
      realInput40InputOneDensity = (5 - Real.sqrt 5) / 10 ∧
      realInput40Memory11 = realInput40InputOneDensity * realInput40InputOneDensity ∧
      xi_real_input40_core_thermodynamic_tail_equivalence_pressure c 0 =
        xi_real_input40_core_thermodynamic_tail_equivalence_corePressure c 0 ∧
      real_input_40_collision_pressure_matrix (vectorPotentialPhiMinusU lam) =
        !![1, 0, 0, 0;
          0, 0, 0, -(3 * vectorPotentialPhiMinusU lam);
          0, 1, 0, 2 - vectorPotentialPhiMinusU lam;
          0, 0, 1, vectorPotentialPhiMinusU lam + 2] ∧
      real_input_40_collision_pressure_charpoly (vectorPotentialPhiMinusU lam) =
        (X - C 1) * real_input_40_collision_pressure_cubic (vectorPotentialPhiMinusU lam) ∧
      vectorPotentialPhiMinusCubic lam (vectorPotentialPhiMinusU lam) = 0 ∧
  real_input_40_collision_pressure_pressure lam =
        vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam) := by
  rcases paper_real_input_40_input_measure_rigid with ⟨hreset, hmarginal, _, _⟩
  have hmarginal_closed := hmarginal
  rcases hmarginal_closed with ⟨_, _, _, h11, hone, _, _, _, _⟩
  have hindependent : realInput40Memory11 = realInput40InputOneDensity * realInput40InputOneDensity := by
    rw [hone, h11]
    have hs : (Real.sqrt 5) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  rcases paper_xi_real_input40_core_thermodynamic_tail_equivalence c θ0 hc with
    ⟨_, _, _, hpressure0, _, _, _, _⟩
  rcases paper_real_input_40_collision_pressure lam hUdenom hAlphaDenom with
    ⟨hmatrix, hcharpoly, hcubic, hpressure⟩
  exact ⟨hreset, hmarginal, hone, hindependent, hpressure0, hmatrix, hcharpoly, hcubic,
    hpressure⟩

end Omega.SyncKernelRealInput
