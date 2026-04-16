import Mathlib.Tactic

namespace Omega.GU.U1ThroatIdentity

/-- Paper-facing seed for the identity between the unification point and the inversion fixed point. -/
theorem paper_gut_u1_throat_identity_seeds {u : ℝ} (hu : 0 < u) :
    u = 1 / u ↔ u = 1 := by
  constructor
  · intro h
    have hu0 : u ≠ 0 := by linarith
    have hsq : u ^ 2 = 1 := by
      have hmul : u * u = 1 := by
        exact (eq_div_iff hu0).mp h
      simpa [pow_two] using hmul
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exact h1
    · linarith
  · intro h
    rw [h]
    norm_num

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_gut_u1_throat_identity_package {u : ℝ} (hu : 0 < u) :
    u = 1 / u ↔ u = 1 :=
  paper_gut_u1_throat_identity_seeds hu

end Omega.GU.U1ThroatIdentity
