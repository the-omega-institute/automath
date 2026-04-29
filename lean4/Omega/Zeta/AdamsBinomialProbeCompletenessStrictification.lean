import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.AdamsBinomialProbeDiscreteInversionEquispacedGrid
import Omega.Zeta.XiCarathPickKernelNormalizationRigidity

namespace Omega.Zeta

open Complex

noncomputable section

/-- Equality of the recovered Laurent coefficient at the minimal window `N = |m|`. -/
def xiAdamsRecoveredProbeFamilyAgree (c₁ c₂ : ℤ → ℂ) : Prop :=
  ∀ m : ℤ,
    adamsRecoveredLaurentCoeffFromGrid m.natAbs 1 c₁ m =
      adamsRecoveredLaurentCoeffFromGrid m.natAbs 1 c₂ m

/-- Equality of all Laurent coefficients, viewed as equality of the finite atomic Herglotz data
encoded by those coefficients. -/
def xiAdamsRecoveredHerglotzMeasuresAgree (c₁ c₂ : ℤ → ℂ) : Prop :=
  ∀ n : ℤ, c₁ n = c₂ n

/-- Concrete strictification statement: the `d = 1` Adams probe family recovers every Laurent
coefficient, so equality of the recovered probe family forces equality of the coefficient data, and
any equality of Carathéodory--Pick kernels then rigidifies the associated Herglotz functions up to
a unique imaginary constant. -/
def xiAdamsBinomialProbeCompletenessStrictificationStatement : Prop :=
  ∀ c₁ c₂ : ℤ → ℂ,
    ∀ F₁ F₂ : ℂ → ℂ,
      xiAdamsRecoveredProbeFamilyAgree c₁ c₂ →
      (∀ w z : ℂ, carathPickKernel F₁ w z = carathPickKernel F₂ w z) →
      xiAdamsRecoveredHerglotzMeasuresAgree c₁ c₂ ∧
        ∃! β : ℝ, ∀ w : ℂ, F₁ w = F₂ w + Complex.I * (β : ℂ)

private lemma int_mem_Icc_natAbs (m : ℤ) :
    m ∈ Finset.Icc (-(m.natAbs : ℤ)) m.natAbs := by
  cases m with
  | ofNat n =>
      simp
  | negSucc n =>
      simp
      omega

private lemma recoveredProbeFamilyAgree_coefficients
    {c₁ c₂ : ℤ → ℂ}
    (hprobe : xiAdamsRecoveredProbeFamilyAgree c₁ c₂) :
    xiAdamsRecoveredHerglotzMeasuresAgree c₁ c₂ := by
  intro n
  let m : ℤ := -n
  have hm : m ∈ Finset.Icc (-(m.natAbs : ℤ)) m.natAbs := int_mem_Icc_natAbs m
  have hrec₁ :=
    (paper_xi_adams_binomial_probe_discrete_inversion_equispaced_grid m.natAbs 1 c₁).2.2.1 m hm
  have hrec₂ :=
    (paper_xi_adams_binomial_probe_discrete_inversion_equispaced_grid m.natAbs 1 c₂).2.2.1 m hm
  calc
    c₁ n = c₁ (-(1 : ℤ) * m) := by simp [m]
    _ = adamsRecoveredLaurentCoeffFromGrid m.natAbs 1 c₁ m := by
      symm
      simpa using hrec₁
    _ = adamsRecoveredLaurentCoeffFromGrid m.natAbs 1 c₂ m := hprobe m
    _ = c₂ (-(1 : ℤ) * m) := by simpa using hrec₂
    _ = c₂ n := by simp [m]

theorem xiAdamsBinomialProbeCompletenessStrictificationStatement_true :
    xiAdamsBinomialProbeCompletenessStrictificationStatement := by
  intro c₁ c₂ F₁ F₂ hprobe hkernel
  refine ⟨recoveredProbeFamilyAgree_coefficients hprobe, ?_⟩
  exact paper_xi_carath_pick_kernel_normalization_rigidity F₁ F₂ hkernel

/-- Paper label: `thm:xi-adams-binomial-probe-completeness-strictification`. -/
def paper_xi_adams_binomial_probe_completeness_strictification : Prop :=
  xiAdamsBinomialProbeCompletenessStrictificationStatement

theorem paper_xi_adams_binomial_probe_completeness_strictification_verified :
    paper_xi_adams_binomial_probe_completeness_strictification :=
  xiAdamsBinomialProbeCompletenessStrictificationStatement_true

end

end Omega.Zeta
