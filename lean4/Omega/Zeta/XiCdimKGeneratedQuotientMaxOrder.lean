import Omega.Zeta.XiCdimLambdaClosedForm

namespace Omega.Zeta

private lemma xi_cdim_k_generated_quotient_max_order_list_prod_pos
    {xs : List ℕ} (hpos : ∀ n ∈ xs, 0 < n) :
    0 < xs.prod := by
  induction xs with
  | nil =>
      simp
  | cons a as ih =>
      have ha : 0 < a := hpos a (by simp)
      have htail : 0 < as.prod := ih (by
        intro n hn
        exact hpos n (by simp [hn]))
      simpa using Nat.mul_pos ha htail

private lemma xi_cdim_k_generated_quotient_max_order_xiCdimLambda_pos
    (factors : List ℕ) (hfac : ∀ n ∈ factors, 1 < n) (k : ℕ) :
    0 < xiCdimLambda factors k := by
  rw [xiCdimLambda]
  apply xi_cdim_k_generated_quotient_max_order_list_prod_pos
  intro n hn
  have hn_factors : n ∈ factors := (List.take_sublist (factors.length - k) factors).subset hn
  exact lt_trans zero_lt_one (hfac n hn_factors)

/-- Paper label: `lem:xi-cdim-k-generated-quotient-max-order`. -/
theorem paper_xi_cdim_k_generated_quotient_max_order (factors : List ℕ)
    (hfac : ∀ n ∈ factors, 1 < n) :
    ∀ k : ℕ, (factors.drop (factors.length - k)).prod = factors.prod / xiCdimLambda factors k := by
  intro k
  rcases paper_xi_cdim_lambda_closed_form factors hfac with ⟨_, hsplit, hone⟩
  by_cases hk : k ≤ factors.length
  · have hprod :
        xiCdimLambda factors k * (factors.drop (factors.length - k)).prod = factors.prod :=
      hsplit k hk
    have hxi_pos : 0 < xiCdimLambda factors k :=
      xi_cdim_k_generated_quotient_max_order_xiCdimLambda_pos factors hfac k
    rw [← hprod, Nat.mul_div_right _ hxi_pos]
  · have hlen : factors.length ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    have hxi : xiCdimLambda factors k = 1 := (hone k).2 hlen
    simp [Nat.sub_eq_zero_of_le hlen, hxi]

end Omega.Zeta
