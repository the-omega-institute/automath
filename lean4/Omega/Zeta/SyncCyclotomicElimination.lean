import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The completed determinant for the sync-cyclotomic elimination step, expressed as a polynomial
in `w` with coefficients polynomial in `s`. -/
noncomputable def sync_cyclotomic_elimination_hat_delta : Polynomial (Polynomial ℤ) :=
  let s : Polynomial ℤ := X
  let w : Polynomial (Polynomial ℤ) := X
  C (1 : Polynomial ℤ)
    - C s * w
    - C (5 : Polynomial ℤ) * w ^ 2
    + C (3 * s) * w ^ 3
    + C ((5 : Polynomial ℤ) - s ^ 2) * w ^ 4
    + C (s ^ 3 - 6 * s) * w ^ 5
    + C (s ^ 2 - 1) * w ^ 6

/-- Evaluate the completed determinant at complex parameters `(w, s)`. -/
noncomputable def sync_cyclotomic_elimination_eval (w s : ℂ) : ℂ :=
  (sync_cyclotomic_elimination_hat_delta.eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) s) w)

/-- The completion substitution `u = r^2`, `w = z r`, `s = r + r⁻¹` expressed directly in the
completed variables. -/
noncomputable def sync_cyclotomic_elimination_completion (r w : ℂ) : ℂ :=
  sync_cyclotomic_elimination_eval w (r + r⁻¹)

lemma sync_cyclotomic_elimination_completion_invariant (r w : ℂ) :
    sync_cyclotomic_elimination_completion r w =
      sync_cyclotomic_elimination_completion r⁻¹ w := by
  simp [sync_cyclotomic_elimination_completion, sync_cyclotomic_elimination_eval, add_comm]

/-- Paper label: `prop:sync-cyclotomic-elimination`. After the completion change of variables
`u = r^2`, `w = z r`, `s = r + r⁻¹`, the sync determinant descends to an element of `ℤ[s][w]`,
and self-duality under `r ↦ r⁻¹` becomes invariance of the completed expression. -/
theorem paper_sync_cyclotomic_elimination :
    ∃ hatDelta : Polynomial (Polynomial ℤ),
      hatDelta = sync_cyclotomic_elimination_hat_delta ∧
      (∀ r w : ℂ,
        sync_cyclotomic_elimination_completion r w =
          hatDelta.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (r + r⁻¹)) w) ∧
      (∀ r w : ℂ,
        sync_cyclotomic_elimination_completion r w =
          sync_cyclotomic_elimination_completion r⁻¹ w) := by
  refine ⟨sync_cyclotomic_elimination_hat_delta, rfl, ?_, ?_⟩
  · intro r w
    rfl
  · intro r w
    exact sync_cyclotomic_elimination_completion_invariant r w

end Omega.Zeta
