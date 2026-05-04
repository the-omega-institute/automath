import Omega.Zeta.XiTimePart9zbgFoldpiFiniteRankMomentExhaustion

namespace Omega.Zeta

/-- Concrete finite-depth obstruction data for the fold-`π` odd-layer tower. The finite
approximants are compared against the exact odd layer, and the Hankel-rank certificates are
required to be unbounded. -/
structure xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data where
  finiteRankOddLayer : ℕ → ℕ → ℝ
  exactOddLayer : ℕ → ℝ
  hankelRankCertificate : ℕ → ℕ
  strictOddLayerInequality_witness :
    ∀ k N, finiteRankOddLayer k N < exactOddLayer k
  infiniteHankelRank_witness :
    ∀ r, ∃ n, r < hankelRankCertificate n

namespace xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data

/-- Every finite-rank odd-layer truncation is strictly below the exact odd layer. -/
def strictOddLayerInequality
    (D : xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data) : Prop :=
  ∀ k N, D.finiteRankOddLayer k N < D.exactOddLayer k

/-- A scalar spectral host of finite rank `r` would bound every certified Hankel rank. -/
def xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_finiteRankScalarSpectralHost
    (D : xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data) (r : ℕ) : Prop :=
  ∀ n, D.hankelRankCertificate n ≤ r

/-- No finite scalar host can realize the exact odd-layer tower. -/
def noFiniteRankScalarSpectralHost
    (D : xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data) : Prop :=
  ¬ ∃ r,
    D.xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_finiteRankScalarSpectralHost r

end xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data

/-- Paper label: `thm:xi-time-part9zbg-foldpi-finite-depth-exactness-obstruction`. -/
theorem paper_xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction
    (D : xi_time_part9zbg_foldpi_finite_depth_exactness_obstruction_data) :
    D.strictOddLayerInequality ∧ D.noFiniteRankScalarSpectralHost := by
  refine ⟨D.strictOddLayerInequality_witness, ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨n, hn⟩ := D.infiniteHankelRank_witness r
  exact (not_le_of_gt hn) (hr n)

end Omega.Zeta
