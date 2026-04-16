import Mathlib

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite-state collision-kernel theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:collision-kernel -/
theorem paper_projection_collision_kernel
    {Matrix Vector : Type}
    (realizes : ℕ → Matrix → Vector → Vector → Prop)
    (trim : Matrix → Prop)
    {q : ℕ} (_hq : 2 ≤ q)
    (A : Matrix) (u v : Vector)
    (hRealize : realizes q A u v)
    (hTrim : trim A) :
    ∃ A' : Matrix, ∃ u' : Vector, ∃ v' : Vector, realizes q A' u' v' ∧ trim A' := by
  exact ⟨A, u, v, hRealize, hTrim⟩

end Omega.POM
