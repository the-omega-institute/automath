import Mathlib.Data.Nat.GCD.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-gcd-rank-fingerprint-rigidity`. -/
theorem paper_conclusion_fibadic_gcd_rank_fingerprint_rigidity (F : ℕ → ℕ)
    (rankFingerprint : ℕ → ℕ → ℕ)
    (hRank : ∀ N m, 3 ≤ N → rankFingerprint N m = F (Nat.gcd m N))
    (hDetect :
      ∀ {N M},
        3 ≤ N →
        3 ≤ M →
        (∀ m, F (Nat.gcd m N) = F (Nat.gcd m M)) →
        N = M) :
    ∀ {N M},
      3 ≤ N →
      3 ≤ M →
      (∀ m, rankFingerprint N m = rankFingerprint M m) →
      N = M := by
  intro N M hN hM hFingerprint
  apply hDetect hN hM
  intro m
  rw [← hRank N m hN, ← hRank M m hM]
  exact hFingerprint m

end Omega.Conclusion
