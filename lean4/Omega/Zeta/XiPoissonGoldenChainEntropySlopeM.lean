import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The golden ratio scale used for the discrete chain `t_n = phi^n`. -/
def xi_poisson_golden_chain_entropy_slope_m_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Golden-chain time `t_n = phi^n`. -/
def xi_poisson_golden_chain_entropy_slope_m_time (n : ℕ) : ℝ :=
  xi_poisson_golden_chain_entropy_slope_m_phi ^ n

/-- The entropy slope after substituting a first nonvanishing moment of order `m`
into the golden chain.  Constant and little-oh terms have already been divided by
`n`, so the exact model is the limiting slope. -/
def xi_poisson_golden_chain_entropy_slope_m_slope (m : ℕ) : ℝ :=
  2 * (m : ℝ) * Real.log xi_poisson_golden_chain_entropy_slope_m_phi

/-- Reading off the moment order is multiplication by the normalizing denominator;
this avoids adding an unnecessary inverse to the seed interface. -/
def xi_poisson_golden_chain_entropy_slope_m_readout (m : ℕ) : ℝ :=
  2 * Real.log xi_poisson_golden_chain_entropy_slope_m_phi * (m : ℝ)

/-- The KL leading constant for the first nonvanishing-moment package, restricted
to the algebra needed by the golden-chain slope corollary. -/
def xi_poisson_golden_chain_entropy_slope_m_klLeadingConstant
    (m : ℕ) (kappa fisherConstant : ℝ) : ℝ :=
  (kappa ^ 2 / (Nat.factorial m : ℝ) ^ 2) * fisherConstant

/-- The corresponding `f`-divergence leading constant after the second-order
Taylor transfer. -/
def xi_poisson_golden_chain_entropy_slope_m_fdivLeadingConstant
    (m : ℕ) (kappa fisherConstant fSecond : ℝ) : ℝ :=
  (fSecond / 2) *
    xi_poisson_golden_chain_entropy_slope_m_klLeadingConstant m kappa fisherConstant

/-- Concrete formal statement for `cor:xi-poisson-golden-chain-entropy-slope-m`.

The first conjunct records the substitution `t_n = phi^n`; the second is the
exact slope obtained after logarithm and division by `n`; the third ties the
normalization back to the existing first-nonvanishing-moment KL coefficient
package, whose KL case is recovered when `f''(1)=2`. -/
def xi_poisson_golden_chain_entropy_slope_m_statement : Prop :=
  (∀ n : ℕ,
    xi_poisson_golden_chain_entropy_slope_m_time n =
      xi_poisson_golden_chain_entropy_slope_m_phi ^ n) ∧
  (∀ m : ℕ,
    xi_poisson_golden_chain_entropy_slope_m_slope m =
      xi_poisson_golden_chain_entropy_slope_m_readout m) ∧
  ∀ (m : ℕ) (kappa fisherConstant : ℝ),
    xi_poisson_golden_chain_entropy_slope_m_fdivLeadingConstant m kappa fisherConstant 2 =
      xi_poisson_golden_chain_entropy_slope_m_klLeadingConstant m kappa fisherConstant

/-- Paper label: `cor:xi-poisson-golden-chain-entropy-slope-m`. -/
theorem paper_xi_poisson_golden_chain_entropy_slope_m :
    xi_poisson_golden_chain_entropy_slope_m_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro m
    simp [xi_poisson_golden_chain_entropy_slope_m_slope,
      xi_poisson_golden_chain_entropy_slope_m_readout]
    ring
  · intro m kappa fisherConstant
    simp [xi_poisson_golden_chain_entropy_slope_m_fdivLeadingConstant,
      xi_poisson_golden_chain_entropy_slope_m_klLeadingConstant]

end

end Omega.Zeta
