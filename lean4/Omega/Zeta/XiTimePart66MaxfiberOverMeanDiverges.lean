import Mathlib.Tactic

namespace Omega.Zeta

/-- Elementary sequential divergence to `+∞`, stated in an order-only form. -/
def xi_time_part66_maxfiber_over_mean_diverges_tendsToInfinity (u : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ u n

/-- Concrete data for the collision-scale lower bound.  `scale m * collision m` abstracts
`F_{m+2} Col_m`, while `ratio m` abstracts `M_m / \bar d_m`. -/
structure xi_time_part66_maxfiber_over_mean_diverges_Data where
  scale : ℕ → ℝ
  collision : ℕ → ℝ
  ratio : ℕ → ℝ
  collisionScale_le_ratio : ∀ m, scale m * collision m ≤ ratio m
  collisionScale_diverges :
    xi_time_part66_maxfiber_over_mean_diverges_tendsToInfinity
      (fun m => scale m * collision m)

namespace xi_time_part66_maxfiber_over_mean_diverges_Data

/-- Pointwise transfer of `Col_m ≤ p_max` after multiplying by the finite scale. -/
def pointwiseLowerBound (D : xi_time_part66_maxfiber_over_mean_diverges_Data) : Prop :=
  ∀ m, D.scale m * D.collision m ≤ D.ratio m

/-- The max-fiber-over-mean ratio diverges. -/
def ratioDiverges (D : xi_time_part66_maxfiber_over_mean_diverges_Data) : Prop :=
  xi_time_part66_maxfiber_over_mean_diverges_tendsToInfinity D.ratio

end xi_time_part66_maxfiber_over_mean_diverges_Data

/-- Paper label: `thm:xi-time-part66-maxfiber-over-mean-diverges`.  The ratio is pointwise
above the normalized collision scale, so divergence of the latter transfers monotonically. -/
theorem paper_xi_time_part66_maxfiber_over_mean_diverges
    (D : xi_time_part66_maxfiber_over_mean_diverges_Data) :
    D.pointwiseLowerBound ∧ D.ratioDiverges := by
  refine ⟨D.collisionScale_le_ratio, ?_⟩
  intro B
  rcases D.collisionScale_diverges B with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact le_trans (hN n hn) (D.collisionScale_le_ratio n)

end Omega.Zeta
