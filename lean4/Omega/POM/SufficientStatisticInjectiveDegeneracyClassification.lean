import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM

private theorem two_pow_half_ceiling_le_fib (l : Nat) : 2 ^ ((l + 1) / 2) ≤ Nat.fib (l + 2) := by
  rcases Nat.even_or_odd l with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : ((k + k + 1) / 2) = k := by omega
    have hindex : k + k + 2 = 2 + 2 * k := by ring
    rw [hk, hindex]
    simpa using Omega.fib_exponential_growth 2 k (by omega)
  · have h := Omega.fib_exponential_growth 3 k (by omega)
    have h3 : Nat.fib 3 = 2 := by native_decide
    have hk : ((2 * k + 1 + 1) / 2) = k + 1 := by omega
    have hindex : 2 * k + 1 + 2 = 3 + 2 * k := by ring
    rw [hk, hindex]
    simpa [h3, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

private theorem two_pow_total_dx_le_total_dm :
    ∀ components : List Nat,
      2 ^ (components.foldr (fun l acc => ((l + 1) / 2) + acc) 0) ≤
        components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1
  | [] => by simp
  | l :: tl => by
      have hl : 2 ^ ((l + 1) / 2) ≤ Nat.fib (l + 2) := two_pow_half_ceiling_le_fib l
      have htl := two_pow_total_dx_le_total_dm tl
      calc
        2 ^ (((l + 1) / 2) + tl.foldr (fun l acc => ((l + 1) / 2) + acc) 0)
            = 2 ^ ((l + 1) / 2) *
                2 ^ (tl.foldr (fun l acc => ((l + 1) / 2) + acc) 0) := by
                  rw [Nat.pow_add]
        _ ≤ Nat.fib (l + 2) * tl.foldr (fun l acc => Nat.fib (l + 2) * acc) 1 :=
              Nat.mul_le_mul hl htl

private theorem total_dm_eq_one_of_total_dx_eq_zero :
    ∀ components : List Nat,
      components.foldr (fun l acc => ((l + 1) / 2) + acc) 0 = 0 →
        components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1 = 1
  | [] => by simp
  | l :: tl => by
      intro hdx
      by_cases hl0 : l = 0
      · have htlx : tl.foldr (fun l acc => ((l + 1) / 2) + acc) 0 = 0 := by
          simpa [hl0] using hdx
        simp [hl0, total_dm_eq_one_of_total_dx_eq_zero tl htlx]
      · have hpos : 0 < ((l + 1) / 2) := by
          exact Nat.div_pos (by omega) (by omega)
        have hsum_pos :
            0 < ((l + 1) / 2) + tl.foldr (fun l acc => ((l + 1) / 2) + acc) 0 :=
          Nat.add_pos_left hpos _
        exact False.elim ((Nat.ne_of_gt hsum_pos) hdx)

private theorem succ_lt_two_pow_of_two_le (n : Nat) (hn : 2 ≤ n) : n + 1 < 2 ^ n := by
  have hlt : n + 1 < 2 * n := by omega
  have hpow : n ≤ 2 ^ (n - 1) := by
    have h : n - 1 < 2 ^ (n - 1) := Nat.lt_pow_self (by norm_num : (1 : Nat) < 2)
    omega
  have htwo : 2 * n ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 hpow
  have hpow' : 2 * 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ ((n - 1) + 1) := by rw [Nat.pow_add, pow_one]
      _ = 2 ^ n := by
            have hnsub : (n - 1) + 1 = n := by omega
            rw [hnsub]
  have htwo' : 2 * n ≤ 2 ^ n := by simpa [hpow'] using htwo
  exact lt_of_lt_of_le hlt htwo'

/-- Paper label: `cor:pom-sufficient-statistic-injective-degeneracy-classification`. The
Fibonacci contribution of each path component dominates the dyadic lower bound coming from the
componentwise ceiling-halves, so only the zero-dimensional and single-edge degeneracies avoid the
strict gap `d_x + 1 < d_m`. -/
theorem paper_pom_sufficient_statistic_injective_degeneracy_classification
    (components : List Nat) :
    let d_m := components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1
    let d_x := components.foldr (fun l acc => ((l + 1) / 2) + acc) 0
    (d_x = 0 /\ d_m = 1) \/ (d_x = 1 /\ d_m = 2) \/ (2 ^ d_x <= d_m /\ d_x + 1 < d_m) := by
  dsimp
  have hlower := two_pow_total_dx_le_total_dm components
  by_cases hdx0 : components.foldr (fun l acc => ((l + 1) / 2) + acc) 0 = 0
  · left
    exact ⟨hdx0, total_dm_eq_one_of_total_dx_eq_zero components hdx0⟩
  · by_cases hdx1 : components.foldr (fun l acc => ((l + 1) / 2) + acc) 0 = 1
    · by_cases hdm2 : components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1 = 2
      · exact Or.inr <| Or.inl ⟨hdx1, hdm2⟩
      · have hdm_ge_two : 2 ≤ components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1 := by
          simpa [hdx1] using hlower
        have hdm_gt_two : 2 < components.foldr (fun l acc => Nat.fib (l + 2) * acc) 1 := by
          omega
        exact Or.inr <| Or.inr <| by
          simpa [hdx1] using And.intro hlower hdm_gt_two
    · have hdx_ge_two : 2 ≤ components.foldr (fun l acc => ((l + 1) / 2) + acc) 0 := by
        omega
      have hgap :
          components.foldr (fun l acc => ((l + 1) / 2) + acc) 0 + 1 <
            2 ^ (components.foldr (fun l acc => ((l + 1) / 2) + acc) 0) :=
        succ_lt_two_pow_of_two_le _ hdx_ge_two
      exact Or.inr <| Or.inr ⟨hlower, lt_of_lt_of_le hgap hlower⟩

end Omega.POM
