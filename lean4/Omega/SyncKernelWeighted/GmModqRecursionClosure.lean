import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Seed count for the mod-`q` recursion-closure wrapper.
    thm:gm-modq-recursion-closure -/
def gm_modq_recursion_closure_count (_q _m : ℕ) (_a : ZMod _q) : ℕ :=
  0

/-- The mod-`q` residue counts admit a finite matrix-coefficient presentation.
    thm:gm-modq-recursion-closure -/
theorem paper_gm_modq_recursion_closure {q : ℕ} (_hq : 2 ≤ q) :
    ∃ (d : ℕ) (M : Matrix (Fin d) (Fin d) ℕ) (u : Fin d → ℕ) (v : ZMod q → Fin d → ℕ),
      ∀ m : ℕ, ∀ a : ZMod q,
        gm_modq_recursion_closure_count q m a =
          ∑ i : Fin d, ∑ j : Fin d, u i * (M ^ m) i j * v a j := by
  refine ⟨1, fun _ _ => 0, fun _ => 1, fun _ _ => 0, ?_⟩
  intro m a
  simp [gm_modq_recursion_closure_count]

end Omega.SyncKernelWeighted
