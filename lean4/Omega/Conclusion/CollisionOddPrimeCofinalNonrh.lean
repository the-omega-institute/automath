import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open Topology

/-- Concrete fourth-order collision-channel data along the cofinal odd-prime scale. -/
structure conclusion_collision_odd_prime_cofinal_nonrh_Context where
  theta : ℕ → ℝ
  twistScale : ℕ → ℝ
  gamma2 : ℝ
  gamma4 : ℝ
  remainder : ℕ → ℝ

/-- The fourth-order expansion around the trivial twist, after substituting the odd-prime scale.
The scale and the remainder both tend to zero, and `theta` agrees eventually with the fourth-order
jet plus the remainder. -/
def conclusion_collision_odd_prime_cofinal_nonrh_Context.fourth_order_expansion
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context) : Prop :=
  Tendsto D.twistScale atTop (𝓝 0) ∧
    Tendsto D.remainder atTop (𝓝 0) ∧
      ∀ᶠ p : ℕ in atTop,
        D.theta p =
          1 - D.gamma2 * (D.twistScale p) ^ 2 +
            D.gamma4 * (D.twistScale p) ^ 4 + D.remainder p

/-- The normalized collision exponent tends back to the trivial-twist value. -/
def conclusion_collision_odd_prime_cofinal_nonrh_Context.theta_tends_to_one
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context) : Prop :=
  Tendsto D.theta atTop (𝓝 1)

/-- The cofinal odd-prime non-RH margin: eventually every odd prime has exponent above `1/2`. -/
def conclusion_collision_odd_prime_cofinal_nonrh_Context.eventually_nonrh
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context) : Prop :=
  ∀ᶠ p : ℕ in atTop, Nat.Prime p → Odd p → 1 / 2 < D.theta p

lemma conclusion_collision_odd_prime_cofinal_nonrh_theta_tendsto
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context)
    (h : D.fourth_order_expansion) : D.theta_tends_to_one := by
  rcases h with ⟨hscale, hremainder, heq⟩
  have hscale2 : Tendsto (fun p : ℕ => (D.twistScale p) ^ 2) atTop (𝓝 0) := by
    simpa using hscale.pow 2
  have hscale4 : Tendsto (fun p : ℕ => (D.twistScale p) ^ 4) atTop (𝓝 0) := by
    simpa using hscale.pow 4
  have hquad : Tendsto (fun p : ℕ => D.gamma2 * (D.twistScale p) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hscale2
  have hquart : Tendsto (fun p : ℕ => D.gamma4 * (D.twistScale p) ^ 4) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hscale4
  have hjet :
      Tendsto
        (fun p : ℕ =>
          1 - D.gamma2 * (D.twistScale p) ^ 2 +
            D.gamma4 * (D.twistScale p) ^ 4 + D.remainder p)
        atTop (𝓝 1) := by
    have hconst : Tendsto (fun _p : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hsub :
        Tendsto (fun p : ℕ => 1 - D.gamma2 * (D.twistScale p) ^ 2) atTop (𝓝 1) := by
      simpa using hconst.sub hquad
    have hadd :
        Tendsto
          (fun p : ℕ =>
            1 - D.gamma2 * (D.twistScale p) ^ 2 + D.gamma4 * (D.twistScale p) ^ 4)
          atTop (𝓝 1) := by
      simpa using hsub.add hquart
    simpa using hadd.add hremainder
  exact hjet.congr' (Filter.EventuallyEq.symm heq)

lemma conclusion_collision_odd_prime_cofinal_nonrh_eventually_nonrh
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context)
    (h : D.theta_tends_to_one) : D.eventually_nonrh := by
  have hgt : ∀ᶠ p : ℕ in atTop, 1 / 2 < D.theta p := by
    have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds (by norm_num)
    exact h.eventually hnhds
  filter_upwards [hgt] with p hp _hprime _hodd
  exact hp

/-- Paper label: `thm:conclusion-collision-odd-prime-cofinal-nonrh`. -/
theorem paper_conclusion_collision_odd_prime_cofinal_nonrh
    (D : conclusion_collision_odd_prime_cofinal_nonrh_Context) :
    D.fourth_order_expansion -> D.theta_tends_to_one ∧ D.eventually_nonrh := by
  intro h
  have htendsto : D.theta_tends_to_one :=
    conclusion_collision_odd_prime_cofinal_nonrh_theta_tendsto D h
  exact ⟨htendsto, conclusion_collision_odd_prime_cofinal_nonrh_eventually_nonrh D htendsto⟩

end Omega.Conclusion
