import Omega.Zeta.XiTimePart9zbkGaussianCompressorUniqueness

namespace Omega.Zeta

/-- Exactness one moment beyond the Gaussian-compressor uniqueness range would give a distinct
finite-depth shadow matching through order `2n + 1`.  The ceiling statement rules this out in the
finite Padé-Jacobi shadow model used by the surrounding part9zbk formalization. -/
def xi_time_part9zbk_positive_natomic_exactness_ceiling_statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ¬ ∃ R : PadeJacobiShadow,
      finiteDepth R ∧ matchesToOrder m_phi R (2 * n + 1) ∧ R ≠ m_phi_n n

/-- Paper label: `thm:xi-time-part9zbk-positive-natomic-exactness-ceiling`. -/
theorem paper_xi_time_part9zbk_positive_natomic_exactness_ceiling :
    xi_time_part9zbk_positive_natomic_exactness_ceiling_statement := by
  intro n hn hExact
  rcases hExact with ⟨R, hFinite, hMatchExtra, hDistinct⟩
  have hUnique := xi_time_part9zbk_gaussian_compressor_uniqueness_verified n hn
  have hMatch : matchesToOrder m_phi R (2 * n) := by
    intro k hk
    exact hMatchExtra k (Nat.lt_of_lt_of_le hk (Nat.le_succ (2 * n)))
  exact hDistinct (hUnique R hFinite hMatch)

end Omega.Zeta
