import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label:
`thm:xi-time-part9m3-all-nonzero-visibility-extinction-divisibility-obstruction`.

If every nonzero Fourier mode vanished, the abstract inversion hypothesis would make every
multiplicity equal to `T / M`. Evaluating this at one residue class already forces `M ∣ T`,
contradicting the assumed divisibility obstruction. -/
theorem paper_xi_time_part9m3_all_nonzero_visibility_extinction_divisibility_obstruction
    {M T : ℕ} (hM : 1 < M) (d : Fin M → ℕ) (A : Fin M → ℂ)
    (hFourier :
      (∀ k : Fin M, k.val ≠ 0 → A k = 0) ↔
        ∀ r : Fin M, (d r : ℚ) = (T : ℚ) / (M : ℚ))
    (hTotal : (∑ r, d r) = T) (hNotDvd : ¬ M ∣ T) :
    ∃ k : Fin M, k.val ≠ 0 ∧ A k ≠ 0 := by
  by_contra hnone
  have hzero : ∀ k : Fin M, k.val ≠ 0 → A k = 0 := by
    intro k hk
    by_contra hAk
    exact hnone ⟨k, hk, hAk⟩
  have huniform : ∀ r : Fin M, (d r : ℚ) = (T : ℚ) / (M : ℚ) := hFourier.mp hzero
  have hMpos : 0 < M := Nat.lt_trans Nat.zero_lt_one hM
  let r0 : Fin M := ⟨0, hMpos⟩
  have hd_eq : ∀ r : Fin M, d r = d r0 := by
    intro r
    have hq : (d r : ℚ) = (d r0 : ℚ) := by
      rw [huniform r, huniform r0]
    exact_mod_cast hq
  have hsum_eq : (∑ r : Fin M, d r) = M * d r0 := by
    calc
      (∑ r : Fin M, d r) = ∑ _r : Fin M, d r0 := by
        exact Finset.sum_congr rfl fun r _ => hd_eq r
      _ = Fintype.card (Fin M) * d r0 := by simp
      _ = M * d r0 := by simp
  have hmulNat : M * d r0 = T := hsum_eq.symm.trans hTotal
  exact hNotDvd ⟨d r0, hmulNat.symm⟩

end Omega.Zeta
