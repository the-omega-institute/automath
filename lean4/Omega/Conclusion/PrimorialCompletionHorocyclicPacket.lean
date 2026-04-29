import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimorialMixedRadixAffine

namespace Omega.Conclusion

open Omega.Conclusion.AffineNormalFormSemidirect
open Omega.Conclusion.PrimorialMixedRadixAffine

/-- Paper label: `cor:conclusion-primorial-completion-horocyclic-packet`. -/
theorem paper_conclusion_primorial_completion_horocyclic_packet (a1 : ℕ) (ha1 : a1 < 2) :
    (∀ k : ℕ, k < 30 →
      (mixedRadixDecode3_1 k = a1 ↔ ∃ j : ℕ, j < 15 ∧ k = a1 + 2 * j)) ∧
    (∀ j : ℕ, j < 15 → A_N_k 30 (a1 + 2 * j) = A_N_k 2 a1 * A_N_k 15 j) := by
  constructor
  · intro k hk
    constructor
    · intro h
      refine ⟨k / 2, ?_, ?_⟩
      · omega
      · calc
          k = k % 2 + 2 * (k / 2) := (Nat.mod_add_div k 2).symm
          _ = a1 + 2 * (k / 2) := by simpa [mixedRadixDecode3_1] using congrArg id h
    · rintro ⟨j, hj, rfl⟩
      simp [mixedRadixDecode3_1]
      interval_cases a1 <;> simp
  · intro j hj
    simpa using (A_N_k_mul 2 15 a1 j (by decide) (by decide)).symm

end Omega.Conclusion
