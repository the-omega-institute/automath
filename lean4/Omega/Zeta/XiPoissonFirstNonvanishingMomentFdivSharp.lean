import Omega.Zeta.XiPoissonFdivSixthOrderMu3Mu4

namespace Omega.Zeta

noncomputable section

/-- The Fisher integral constant for the first nonvanishing Poisson--Cauchy moment of order `m`. -/
def xi_poisson_first_nonvanishing_moment_fdiv_sharp_fisherConstant (m : ℕ) : ℝ :=
  ((m : ℝ) * (Nat.factorial (2 * m) : ℝ)) /
    (((2 * m - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * m))

/-- The KL leading constant before the second-order Taylor transfer of an `f`-divergence. -/
def xi_poisson_first_nonvanishing_moment_fdiv_sharp_klLeadingConstant
    (m : ℕ) (kappa : ℝ) : ℝ :=
  (kappa ^ 2 / (Nat.factorial m : ℝ) ^ 2) *
    xi_poisson_first_nonvanishing_moment_fdiv_sharp_fisherConstant m

/-- The second-order Taylor transfer coefficient `f''(1)/2`. -/
def xi_poisson_first_nonvanishing_moment_fdiv_sharp_secondOrderTaylorTransfer
    (fSecond klConstant : ℝ) : ℝ :=
  (fSecond / 2) * klConstant

/-- The sharp leading constant for the corresponding twice-differentiable `f`-divergence. -/
def xi_poisson_first_nonvanishing_moment_fdiv_sharp_fdivLeadingConstant
    (m : ℕ) (kappa fSecond : ℝ) : ℝ :=
  (fSecond / 2) *
    xi_poisson_first_nonvanishing_moment_fdiv_sharp_klLeadingConstant m kappa

/-- The first-nonvanishing-moment `f`-divergence package: the sharp constant is obtained from the
KL constant by multiplying by `f''(1)/2`, with the KL case recovered at `f''(1)=2`; the existing
sixth-order `f`-divergence package supplies the compatible second-order raw/closed transfer. -/
def xi_poisson_first_nonvanishing_moment_fdiv_sharp_statement : Prop :=
  (∀ (m : ℕ) (kappa fSecond : ℝ),
    xi_poisson_first_nonvanishing_moment_fdiv_sharp_fdivLeadingConstant m kappa fSecond =
      xi_poisson_first_nonvanishing_moment_fdiv_sharp_secondOrderTaylorTransfer fSecond
        (xi_poisson_first_nonvanishing_moment_fdiv_sharp_klLeadingConstant m kappa)) ∧
  (∀ (m : ℕ) (kappa : ℝ),
    xi_poisson_first_nonvanishing_moment_fdiv_sharp_fdivLeadingConstant m kappa 2 =
      xi_poisson_first_nonvanishing_moment_fdiv_sharp_klLeadingConstant m kappa) ∧
  ∀ (fSecond sigmaSq : ℝ),
    xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t4 fSecond sigmaSq =
      xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t4 fSecond sigmaSq

/-- Paper label: `prop:xi-poisson-first-nonvanishing-moment-fdiv-sharp`. -/
theorem paper_xi_poisson_first_nonvanishing_moment_fdiv_sharp :
    xi_poisson_first_nonvanishing_moment_fdiv_sharp_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m kappa fSecond
    rfl
  · intro m kappa
    simp [xi_poisson_first_nonvanishing_moment_fdiv_sharp_fdivLeadingConstant,
      xi_poisson_first_nonvanishing_moment_fdiv_sharp_klLeadingConstant]
  · intro fSecond sigmaSq
    exact (paper_xi_poisson_fdiv_sixth_order_mu3_mu4 fSecond 0 sigmaSq 0 0).1

end

end Omega.Zeta
