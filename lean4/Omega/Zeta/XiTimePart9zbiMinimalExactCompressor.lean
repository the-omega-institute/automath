import Omega.Zeta.XiTimePart9zbkGaussianCompressorUniqueness

namespace Omega.Zeta

/-- Paper-facing statement for the minimal exact compressor in the finite Padé-Jacobi model:
the canonical `n`-dimensional shadow is the unique finite-depth compressor matching the host
through order `2n`. -/
def xi_time_part9zbi_minimal_exact_compressor_statement (n : ℕ) : Prop :=
  IsUniquePadeJacobiShadow m_phi (m_phi_n n) n

/-- The minimal exact compressor statement is exactly the already verified Gaussian-compressor
uniqueness package from the neighboring part9zbk development. -/
theorem xi_time_part9zbi_minimal_exact_compressor_verified (n : ℕ) (hn : 1 ≤ n) :
    xi_time_part9zbi_minimal_exact_compressor_statement n := by
  simpa [xi_time_part9zbi_minimal_exact_compressor_statement] using
    xi_time_part9zbk_gaussian_compressor_uniqueness_verified n hn

/-- Paper label: `thm:xi-time-part9zbi-minimal-exact-compressor`. -/
def paper_xi_time_part9zbi_minimal_exact_compressor (n : ℕ) (_hn : 1 ≤ n) : Prop :=
  xi_time_part9zbi_minimal_exact_compressor_statement n

end Omega.Zeta
