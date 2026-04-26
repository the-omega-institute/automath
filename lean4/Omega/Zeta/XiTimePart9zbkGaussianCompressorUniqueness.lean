import Omega.Zeta.XiTimePart9zbkPadeJacobiIdentity

namespace Omega.Zeta

/-- Concrete proposition recording the uniqueness of the canonical finite-depth Gaussian
compressor shadow at every positive order. -/
def xi_time_part9zbk_gaussian_compressor_uniqueness_statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsUniquePadeJacobiShadow m_phi (m_phi_n n) n

/-- The Gaussian-compressor uniqueness statement is exactly the previously verified Padé-Jacobi
uniqueness package. -/
theorem xi_time_part9zbk_gaussian_compressor_uniqueness_verified :
    xi_time_part9zbk_gaussian_compressor_uniqueness_statement := by
  intro n hn
  exact paper_xi_time_part9zbk_pade_jacobi_identity n hn

/-- Paper label: `thm:xi-time-part9zbk-gaussian-compressor-uniqueness`.
The requested paper-facing name is the concrete proposition asserting uniqueness of the canonical
finite-depth Gaussian compressor shadow. -/
def paper_xi_time_part9zbk_gaussian_compressor_uniqueness : Prop := by
  exact xi_time_part9zbk_gaussian_compressor_uniqueness_statement

end Omega.Zeta
