import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-truncated-smith-ledger-infinite-indistinguishability`.
Changing only the last Smith coordinate by powers of an outside prime is invisible to any ledger
that is assumed insensitive to those changes, and the powers give infinitely many distinct data. -/
theorem paper_conclusion_truncated_smith_ledger_infinite_indistinguishability {β : Type*}
    (m : ℕ) (ledger : (Fin (m + 1) → ℕ) → β) (d : Fin (m + 1) → ℕ) (ell : ℕ)
    (hledger : ∀ r : ℕ,
      ledger (fun i => if i = Fin.last m then ell ^ r * d i else d i) = ledger d)
    (hd : 0 < d (Fin.last m)) (hell : 2 ≤ ell) :
    ∃ D : ℕ → Fin (m + 1) → ℕ,
      Function.Injective D ∧ ∀ r, ledger (D r) = ledger d := by
  let D : ℕ → Fin (m + 1) → ℕ :=
    fun r i => if i = Fin.last m then ell ^ r * d i else d i
  refine ⟨D, ?_, ?_⟩
  · intro r s hrs
    have hlast := congrFun hrs (Fin.last m)
    have hpow : ell ^ r = ell ^ s := by
      apply Nat.eq_of_mul_eq_mul_right hd
      simpa [D] using hlast
    exact Nat.pow_right_injective (by omega) hpow
  · intro r
    exact hledger r

end Omega.Conclusion
