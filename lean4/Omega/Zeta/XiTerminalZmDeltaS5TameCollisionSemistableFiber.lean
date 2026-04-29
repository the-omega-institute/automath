import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDeltaS5TameCollisionEtaleQuotientNodeLaw

namespace Omega.Zeta

open XiTerminalZmDeltaS5TameCollisionEtaleQuotientData

/-- Specializing the tame-collision quotient-node law to the free action case gives `60` nodes,
and the normalization genus is the recorded genus-`49` input. The extra ramification hypotheses
package the geometric input used in the paper statement. -/
theorem paper_xi_terminal_zm_delta_s5_tame_collision_semistable_fiber
    (D : Omega.Zeta.XiTerminalZmDeltaS5TameCollisionEtaleQuotientData)
    (irreducibleSpecialFiber twoRamificationPoints ramificationIndexFive : Prop)
    (hStab : D.stabilizerOrder = 1) (hIrred : irreducibleSpecialFiber)
    (hRam : twoRamificationPoints) (hIdx : ramificationIndexFive)
    (hGenus : D.normalizedGenus = 49) :
    irreducibleSpecialFiber ∧ D.nodeCount = 60 ∧ D.normalizedGenus = 49 := by
  let _ : twoRamificationPoints := hRam
  let _ : ramificationIndexFive := hIdx
  have hNodeCount : D.nodeCount = 60 := by
    calc
      D.nodeCount = 60 / D.stabilizerOrder := D.nodeCountLaw_holds
      _ = 60 / 1 := by rw [hStab]
      _ = 60 := by norm_num
  exact ⟨hIrred, hNodeCount, hGenus⟩

end Omega.Zeta
