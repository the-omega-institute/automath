import Mathlib.Tactic
import Omega.Core.PowerInequality

namespace Omega.Conclusion

private lemma conclusion_single_collapse_collision_sharpp_complete_strict_of_even_lt
    (q N s t : ℕ) (hq : 2 ≤ q) (hsN : s ≤ N) (htN : t ≤ N) (hsEven : Even s)
    (htEven : Even t) (hst : s < t) :
    s ^ q + (N - s) < t ^ q + (N - t) := by
  rcases hsEven with ⟨a, hs_eq⟩
  rcases htEven with ⟨b, ht_eq_even⟩
  let k : ℕ := t - s
  have hk_pos : 0 < k := by
    dsimp [k]
    omega
  have hk_two : 2 ≤ k := by
    dsimp [k]
    omega
  have ht_eq : t = s + k := by
    dsimp [k]
    omega
  have hpow_gap : s ^ q + k < t ^ q := by
    by_cases hs0 : s = 0
    · have ht_as_k : t = k := by
        dsimp [k]
        omega
      have hk_lt_pow : k < k ^ q := by
        simpa using Nat.pow_lt_pow_right (by omega : 1 < k) (by omega : 1 < q)
      have hq_ne_zero : q ≠ 0 := by omega
      simpa [hs0, ht_as_k, hq_ne_zero] using hk_lt_pow
    · have hsuper :
          s ^ q + k ^ q + 1 ≤ (s + k) ^ q :=
        Omega.pow_add_strict_super s k q (by omega) (by omega) hq
      have hk_le_pow : k ≤ k ^ q := by
        simpa using Nat.pow_le_pow_right hk_pos (by omega : 1 ≤ q)
      rw [← ht_eq] at hsuper
      omega
  have hleft : s ^ q + (N - s) = (s ^ q + k) + (N - t) := by
    omega
  rw [hleft]
  exact Nat.add_lt_add_right hpow_gap (N - t)

/-- Paper label: `thm:conclusion-single-collapse-collision-sharpp-complete`. -/
theorem paper_conclusion_single_collapse_collision_sharpp_complete
    (q N s t : ℕ) (hq : 2 ≤ q) (hsN : s ≤ N) (htN : t ≤ N) (hsEven : Even s)
    (htEven : Even t) (hS : s ^ q + (N - s) = t ^ q + (N - t)) :
    s = t := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hst | hts
  · have hlt :=
      conclusion_single_collapse_collision_sharpp_complete_strict_of_even_lt q N s t hq hsN
        htN hsEven htEven hst
    rw [hS] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · have hlt :=
      conclusion_single_collapse_collision_sharpp_complete_strict_of_even_lt q N t s hq htN
        hsN htEven hsEven hts
    rw [hS.symm] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

end Omega.Conclusion
