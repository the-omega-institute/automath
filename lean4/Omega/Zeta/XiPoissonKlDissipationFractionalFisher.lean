import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-point nonlocal Dirichlet package for Poisson KL dissipation.  The generator
identity supplies the derivative computation; the Fisher term is the logarithmic Dirichlet
integrand with a positive symmetric kernel weight. -/
structure xi_poisson_kl_dissipation_fractional_fisher_data where
  xi_poisson_kl_dissipation_fractional_fisher_ratioLeft : ℝ
  xi_poisson_kl_dissipation_fractional_fisher_ratioRight : ℝ
  xi_poisson_kl_dissipation_fractional_fisher_kernelWeight : ℝ
  xi_poisson_kl_dissipation_fractional_fisher_klDerivative : ℝ
  xi_poisson_kl_dissipation_fractional_fisher_ratioLeft_pos :
    0 < xi_poisson_kl_dissipation_fractional_fisher_ratioLeft
  xi_poisson_kl_dissipation_fractional_fisher_ratioRight_pos :
    0 < xi_poisson_kl_dissipation_fractional_fisher_ratioRight
  xi_poisson_kl_dissipation_fractional_fisher_kernelWeight_pos :
    0 < xi_poisson_kl_dissipation_fractional_fisher_kernelWeight
  xi_poisson_kl_dissipation_fractional_fisher_generator_identity :
    xi_poisson_kl_dissipation_fractional_fisher_klDerivative =
      -xi_poisson_kl_dissipation_fractional_fisher_kernelWeight *
        ((xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
            xi_poisson_kl_dissipation_fractional_fisher_ratioRight) *
          (Real.log xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
            Real.log xi_poisson_kl_dissipation_fractional_fisher_ratioRight))

/-- The fractional Fisher Dirichlet integrand. -/
noncomputable def xi_poisson_kl_dissipation_fractional_fisher_data.fractionalFisher
    (D : xi_poisson_kl_dissipation_fractional_fisher_data) : ℝ :=
  D.xi_poisson_kl_dissipation_fractional_fisher_kernelWeight *
    ((D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
        D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight) *
      (Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
        Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight))

/-- KL derivative equals minus the fractional Fisher dissipation. -/
def xi_poisson_kl_dissipation_fractional_fisher_data.klDerivativeIdentity
    (D : xi_poisson_kl_dissipation_fractional_fisher_data) : Prop :=
  D.xi_poisson_kl_dissipation_fractional_fisher_klDerivative = -D.fractionalFisher

/-- Positivity of the logarithmic Dirichlet form. -/
def xi_poisson_kl_dissipation_fractional_fisher_data.fractionalFisherNonnegative
    (D : xi_poisson_kl_dissipation_fractional_fisher_data) : Prop :=
  0 ≤ D.fractionalFisher

/-- Vanishing Fisher dissipation is equivalent to equality of the density ratios. -/
def xi_poisson_kl_dissipation_fractional_fisher_data.zeroFisherIffEqual
    (D : xi_poisson_kl_dissipation_fractional_fisher_data) : Prop :=
  D.fractionalFisher = 0 ↔
    D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft =
      D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight

lemma xi_poisson_kl_dissipation_fractional_fisher_log_dirichlet_nonnegative
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  by_cases hab : a ≤ b
  · have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    nlinarith
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have hlog : Real.log b ≤ Real.log a := Real.log_le_log hb hba
    nlinarith

lemma xi_poisson_kl_dissipation_fractional_fisher_log_dirichlet_eq_zero
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b) * (Real.log a - Real.log b) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hsub | hlogsub
    · exact sub_eq_zero.mp hsub
    · exact Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb)
        (sub_eq_zero.mp hlogsub)
  · intro h
    simp [h]

/-- Paper label: `prop:xi-poisson-kl-dissipation-fractional-fisher`. -/
theorem paper_xi_poisson_kl_dissipation_fractional_fisher
    (D : xi_poisson_kl_dissipation_fractional_fisher_data) :
    D.klDerivativeIdentity ∧ D.fractionalFisherNonnegative ∧ D.zeroFisherIffEqual := by
  have hdir_nonneg :
      0 ≤
        (D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
            D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight) *
          (Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
            Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight) :=
    xi_poisson_kl_dissipation_fractional_fisher_log_dirichlet_nonnegative
      D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft
      D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight
      D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft_pos
      D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight_pos
  refine ⟨?_, ?_, ?_⟩
  · simpa [xi_poisson_kl_dissipation_fractional_fisher_data.klDerivativeIdentity,
      xi_poisson_kl_dissipation_fractional_fisher_data.fractionalFisher,
      neg_mul] using D.xi_poisson_kl_dissipation_fractional_fisher_generator_identity
  · exact mul_nonneg
      (le_of_lt D.xi_poisson_kl_dissipation_fractional_fisher_kernelWeight_pos)
      hdir_nonneg
  · constructor
    · intro hFisher
      have hweight_ne :
          D.xi_poisson_kl_dissipation_fractional_fisher_kernelWeight ≠ 0 :=
        ne_of_gt D.xi_poisson_kl_dissipation_fractional_fisher_kernelWeight_pos
      have hdir :
          (D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
              D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight) *
            (Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft -
              Real.log D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight) = 0 := by
        exact (mul_eq_zero.mp
          (by
            simpa [xi_poisson_kl_dissipation_fractional_fisher_data.zeroFisherIffEqual,
              xi_poisson_kl_dissipation_fractional_fisher_data.fractionalFisher] using hFisher)).resolve_left
          hweight_ne
      exact
        (xi_poisson_kl_dissipation_fractional_fisher_log_dirichlet_eq_zero
          D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft
          D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight
          D.xi_poisson_kl_dissipation_fractional_fisher_ratioLeft_pos
          D.xi_poisson_kl_dissipation_fractional_fisher_ratioRight_pos).mp hdir
    · intro hEq
      simp [xi_poisson_kl_dissipation_fractional_fisher_data.fractionalFisher, hEq]

end Omega.Zeta
