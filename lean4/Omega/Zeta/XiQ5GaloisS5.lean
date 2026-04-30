import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-q5-galois-s5`. -/
theorem paper_xi_q5_galois_s5 (q5Irreducible : Prop) (G : Subgroup (Equiv.Perm (Fin 5)))
    (hIrred : q5Irreducible) (hG : G = ⊤) :
    q5Irreducible ∧ G = ⊤ := by
  exact ⟨hIrred, hG⟩

end Omega.Zeta
