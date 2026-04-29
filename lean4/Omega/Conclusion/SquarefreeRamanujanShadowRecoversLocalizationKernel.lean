import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-squarefree-ramanujan-shadow-recovers-localization-kernel`. -/
theorem paper_conclusion_squarefree_ramanujan_shadow_recovers_localization_kernel
    (S T : ℕ → Prop) [DecidablePred S] [DecidablePred T] (A : ℕ → ℤ)
    (hS : ∀ p, Nat.Prime p → A p = if S p then (p : ℤ) - 1 else -1)
    (hT : ∀ p, Nat.Prime p → A p = if T p then (p : ℤ) - 1 else -1) :
    (∀ p, Nat.Prime p → (p : ℤ) * (if S p then 1 else 0) = 1 + A p) ∧
      (∀ p, Nat.Prime p → (S p ↔ T p)) := by
  constructor
  · intro p hp
    by_cases hSp : S p
    · simp [hSp, hS p hp]
    · simp [hSp, hS p hp]
  · intro p hp
    have hEq :
        (if S p then (p : ℤ) - 1 else -1) =
          (if T p then (p : ℤ) - 1 else -1) := by
      rw [← hS p hp, ← hT p hp]
    by_cases hSp : S p <;> by_cases hTp : T p
    · exact ⟨fun _ => hTp, fun _ => hSp⟩
    · exfalso
      have hpInt : (p : ℤ) = 0 := by
        linarith [show (p : ℤ) - 1 = -1 by simpa [hSp, hTp] using hEq]
      exact hp.ne_zero (Int.ofNat_eq_zero.mp hpInt)
    · exfalso
      have hpInt : (p : ℤ) = 0 := by
        linarith [show -1 = (p : ℤ) - 1 by simpa [hSp, hTp] using hEq]
      exact hp.ne_zero (Int.ofNat_eq_zero.mp hpInt)
    · exact ⟨fun h => (hSp h).elim, fun h => (hTp h).elim⟩

end Omega.Conclusion
