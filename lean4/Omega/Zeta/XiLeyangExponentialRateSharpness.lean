import Mathlib.Tactic

namespace Omega.Zeta

/--
Concrete first-order sharpness package for
`prop:xi-leyang-exponential-rate-sharpness`.

The fields isolate the nonzero first-order term in the two-conjugate-pair
expansion and the transfer from reciprocal xi-coordinates to zeta-coordinates.
-/
structure xi_leyang_exponential_rate_sharpness_data where
  xi_leyang_exponential_rate_sharpness_nearestRadius : ℝ
  xi_leyang_exponential_rate_sharpness_secondRadius : ℝ
  xi_leyang_exponential_rate_sharpness_firstOrderCoeff : ℝ
  xi_leyang_exponential_rate_sharpness_start : ℕ
  xi_leyang_exponential_rate_sharpness_xiError : ℕ → ℝ
  xi_leyang_exponential_rate_sharpness_zetaError : ℕ → ℝ
  xi_leyang_exponential_rate_sharpness_nearest_positive :
    0 < xi_leyang_exponential_rate_sharpness_nearestRadius
  xi_leyang_exponential_rate_sharpness_second_positive :
    0 < xi_leyang_exponential_rate_sharpness_secondRadius
  xi_leyang_exponential_rate_sharpness_gap :
    xi_leyang_exponential_rate_sharpness_nearestRadius <
      xi_leyang_exponential_rate_sharpness_secondRadius
  xi_leyang_exponential_rate_sharpness_firstOrderCoeff_ne_zero :
    xi_leyang_exponential_rate_sharpness_firstOrderCoeff ≠ 0
  xi_leyang_exponential_rate_sharpness_xi_first_order :
    ∀ n,
      xi_leyang_exponential_rate_sharpness_start ≤ n →
        xi_leyang_exponential_rate_sharpness_xiError n =
          |xi_leyang_exponential_rate_sharpness_firstOrderCoeff| *
            (xi_leyang_exponential_rate_sharpness_nearestRadius /
              xi_leyang_exponential_rate_sharpness_secondRadius) ^ n
  xi_leyang_exponential_rate_sharpness_zeta_transfer :
    ∀ n,
      xi_leyang_exponential_rate_sharpness_start ≤ n →
        xi_leyang_exponential_rate_sharpness_zetaError n =
          xi_leyang_exponential_rate_sharpness_nearestRadius *
            xi_leyang_exponential_rate_sharpness_xiError n

namespace xi_leyang_exponential_rate_sharpness_data

/-- The zeta-plane error has the sharp exponential lower bound. -/
def xi_leyang_exponential_rate_sharpness_statement
    (D : xi_leyang_exponential_rate_sharpness_data) : Prop :=
  ∃ c : ℝ,
    c ≠ 0 ∧
      ∃ n₁ : ℕ,
        ∀ n,
          n₁ ≤ n →
            |c| * D.xi_leyang_exponential_rate_sharpness_nearestRadius *
                (D.xi_leyang_exponential_rate_sharpness_nearestRadius /
                  D.xi_leyang_exponential_rate_sharpness_secondRadius) ^ n ≤
              D.xi_leyang_exponential_rate_sharpness_zetaError n

end xi_leyang_exponential_rate_sharpness_data

/-- Paper label: `prop:xi-leyang-exponential-rate-sharpness`. -/
theorem paper_xi_leyang_exponential_rate_sharpness
    (D : xi_leyang_exponential_rate_sharpness_data) :
    D.xi_leyang_exponential_rate_sharpness_statement := by
  refine ⟨D.xi_leyang_exponential_rate_sharpness_firstOrderCoeff,
    D.xi_leyang_exponential_rate_sharpness_firstOrderCoeff_ne_zero,
      D.xi_leyang_exponential_rate_sharpness_start, ?_⟩
  intro n hn
  rw [D.xi_leyang_exponential_rate_sharpness_zeta_transfer n hn,
    D.xi_leyang_exponential_rate_sharpness_xi_first_order n hn]
  ring_nf
  exact le_rfl

end Omega.Zeta
