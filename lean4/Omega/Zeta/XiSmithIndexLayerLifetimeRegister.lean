import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-smith-index-layer-lifetime-register`. -/
theorem paper_xi_smith_index_layer_lifetime_register {m n : ℕ} (hmn : m ≤ n)
    (e : Fin m → ℕ) :
    (∀ k : ℕ, 1 ≤ k →
      Omega.Zeta.smithPrefixDelta e k =
        ((Finset.univ : Finset (Fin m)).filter fun i => k ≤ e i).card) ∧
    (∀ k : ℕ, 1 ≤ k →
      (k * (n - m) + Omega.Zeta.smithPrefixValue e k) -
          ((k - 1) * (n - m) + Omega.Zeta.smithPrefixValue e (k - 1)) =
        (n - m) + Omega.Zeta.smithPrefixDelta e k) ∧
    (m = n →
      (∑ k ∈ Finset.range (Omega.Zeta.smithPrefixTop e + 1),
          Omega.Zeta.smithPrefixDelta e (k + 1)) =
        ∑ i, e i) := by
  have _paper_xi_smith_index_layer_lifetime_register_hmn_used :
      n - m + m = n := Nat.sub_add_cancel hmn
  refine ⟨?_, ?_, ?_⟩
  · intro k _hk
    simp [Omega.Zeta.smithPrefixDelta]
  · intro k hk
    have hstep :
        Omega.Zeta.smithPrefixValue e k =
          Omega.Zeta.smithPrefixValue e (k - 1) + Omega.Zeta.smithPrefixDelta e k := by
      simpa [Nat.sub_add_cancel hk] using
        Omega.Zeta.smithPrefix_succ_eq_add_delta e (k - 1)
    let a := n - m
    let b := (k - 1) * a + Omega.Zeta.smithPrefixValue e (k - 1)
    let c := a + Omega.Zeta.smithPrefixDelta e k
    have hmain :
        k * a + Omega.Zeta.smithPrefixValue e k = b + c := by
      dsimp [b, c, a]
      rw [hstep]
      have hk_mul : k * (n - m) = (k - 1) * (n - m) + (n - m) := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [Nat.add_mul, one_mul]
      omega
    dsimp [b, c, a] at hmain ⊢
    rw [hmain]
    omega
  · intro _hmn_eq
    have hmono : Monotone (Omega.Zeta.smithPrefixValue e) := by
      intro a b hab
      unfold Omega.Zeta.smithPrefixValue
      exact Finset.sum_le_sum fun i _ => min_le_min_left (e i) hab
    have htel :
        (∑ k ∈ Finset.range (Omega.Zeta.smithPrefixTop e + 1),
            (Omega.Zeta.smithPrefixValue e (k + 1) -
              Omega.Zeta.smithPrefixValue e k)) =
          Omega.Zeta.smithPrefixValue e (Omega.Zeta.smithPrefixTop e + 1) -
            Omega.Zeta.smithPrefixValue e 0 := by
      simpa using
        Finset.sum_range_tsub (f := Omega.Zeta.smithPrefixValue e) hmono
          (Omega.Zeta.smithPrefixTop e + 1)
    calc
      (∑ k ∈ Finset.range (Omega.Zeta.smithPrefixTop e + 1),
          Omega.Zeta.smithPrefixDelta e (k + 1))
          =
        ∑ k ∈ Finset.range (Omega.Zeta.smithPrefixTop e + 1),
          (Omega.Zeta.smithPrefixValue e (k + 1) -
            Omega.Zeta.smithPrefixValue e k) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            exact Omega.Zeta.smithPrefixDelta_eq_sub e k
      _ = Omega.Zeta.smithPrefixValue e (Omega.Zeta.smithPrefixTop e + 1) -
            Omega.Zeta.smithPrefixValue e 0 := htel
      _ = ∑ i, e i := by
            rw [Omega.Zeta.smithPrefixValue_eq_total_of_le_top e
              (Omega.Zeta.smithPrefixTop e + 1) (Nat.le_succ _)]
            simp [Omega.Zeta.smithPrefixValue]

end Omega.Zeta
