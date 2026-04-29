import Mathlib.Tactic

namespace Omega.Zeta

private lemma xi_time_part9x_serrin_ray_exact_capacity_card_range_filter_mod
    (n N r : ℕ) (hN : 0 < N) (hr : r < N) :
    ((Finset.range n).filter (fun ρ => ρ % N = r)).card =
      n / N + (if r < n % N then 1 else 0) := by
  let q := n / N
  let s := n % N
  let C := q + if r < s then 1 else 0
  have hs : s < N := by
    exact Nat.mod_lt n hN
  have hn : n = N * q + s := by
    simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod n N).symm
  have hcard :
      (Finset.range C).card =
        ((Finset.range n).filter (fun ρ => ρ % N = r)).card := by
    refine Finset.card_bij (s := Finset.range C)
      (t := (Finset.range n).filter (fun ρ => ρ % N = r))
      (i := fun k _ => N * k + r) ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range]
      have hkC : k < C := Finset.mem_range.mp hk
      have hk_cases : k < q ∨ k = q ∧ r < s := by
        by_cases hrs : r < s
        · have hk_le : k ≤ q := by
            simpa [C, hrs, Nat.lt_succ_iff] using hkC
          by_cases hkq : k < q
          · exact Or.inl hkq
          · exact Or.inr ⟨le_antisymm hk_le (Nat.not_lt.mp hkq), hrs⟩
        · exact Or.inl (by simpa [C, hrs] using hkC)
      constructor
      · rcases hk_cases with hkq | ⟨rfl, hrs⟩
        · calc
            N * k + r < N * k + N := Nat.add_lt_add_left hr _
            _ = N * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ ≤ N * q := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hkq)
            _ ≤ N * q + s := Nat.le_add_right _ _
            _ = n := hn.symm
        · calc
            N * q + r < N * q + s := Nat.add_lt_add_left hrs _
            _ = n := hn.symm
      · have hmod :
            (r + N * k) % N = r := by
          simp [Nat.mod_eq_of_lt hr, Nat.add_mul_mod_self_left]
        simpa [Nat.add_comm] using hmod
    · intro a _ b _ hab
      exact Nat.mul_left_cancel hN (Nat.add_right_cancel hab)
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rcases ha with ⟨han, hmod⟩
      have hrepr : N * (a / N) + r = a := by
        rw [Nat.add_comm, ← hmod, Nat.mod_add_div]
      refine ⟨a / N, ?_, ?_⟩
      · rw [Finset.mem_range]
        have ha_lt_succ : a < (q + 1) * N := by
          calc
            a < n := han
            _ = N * q + s := hn
            _ < N * q + N := Nat.add_lt_add_left hs _
            _ = N * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = (q + 1) * N := Nat.mul_comm _ _
        have ha_div_le : a / N ≤ q := by
          exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hN).mpr ha_lt_succ)
        by_cases haq : a / N < q
        · exact lt_of_lt_of_le haq (Nat.le_add_right _ _)
        · have hdiv_eq : a / N = q := le_antisymm ha_div_le (Nat.not_lt.mp haq)
          have hrs : r < s := by
            have : N * q + r < N * q + s := by
              calc
                N * q + r = N * (a / N) + r := by rw [hdiv_eq]
                _ = a := hrepr
                _ < n := han
                _ = N * q + s := hn
            exact Nat.lt_of_add_lt_add_left this
          simpa [C, hrs]
      · exact hrepr
  calc
    ((Finset.range n).filter (fun ρ => ρ % N = r)).card = (Finset.range C).card :=
      hcard.symm
    _ = C := by simp
    _ = n / N + (if r < n % N then 1 else 0) := by
      simp [C, q, s]

set_option linter.unusedVariables false

/-- Paper label: `cor:xi-time-part9x-serrin-ray-exact-capacity`. -/
theorem paper_xi_time_part9x_serrin_ray_exact_capacity (m r : ℕ) (hm : 1 ≤ m) :
    let N := Nat.fib (m + 2)
    0 < N →
      r < N →
        ((Finset.range (2 ^ m)).filter (fun ρ => ρ % N = r)).card =
          2 ^ m / N + (if r < 2 ^ m % N then 1 else 0) := by
  dsimp
  clear hm
  intro hN hr
  exact xi_time_part9x_serrin_ray_exact_capacity_card_range_filter_mod
    (n := 2 ^ m) (N := Nat.fib (m + 2)) (r := r) hN hr

end Omega.Zeta
