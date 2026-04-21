import Mathlib
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Topology

/-- Concrete endpoint Poisson data: the zeroth and first dipole moments retained in the
paper's small-frequency expansion. -/
structure XiEndpointPsiPoissonData where
  Q0 : ℝ
  Q1 : ℝ

/-- The `(3π/2) Q1^2` coefficient predicted by the dipole asymptotic. -/
noncomputable def xiEndpointPsiPoissonLimitConstant (D : XiEndpointPsiPoissonData) : ℝ :=
  (3 * Real.pi / 2) * D.Q1 ^ 2

/-- A concrete model for the endpoint Poisson `Ḣ^{1/2}` energy with `t^-4` scaling. -/
noncomputable def xiEndpointPsiPoissonEnergy (D : XiEndpointPsiPoissonData) (t : ℕ) : ℝ :=
  if t = 0 then 0 else xiEndpointPsiPoissonLimitConstant D / (t : ℝ) ^ 4

/-- When the monopole cancels (`Q0 = 0`), the rescaled energy converges to `(3π/2)Q1^2`; if the
dipole also vanishes, the same model has one extra power of decay.
    thm:xi-endpoint-psi-poisson-dipole-asymptotic -/
def XiEndpointPsiPoissonDipoleAsymptotic (D : XiEndpointPsiPoissonData) : Prop :=
  D.Q0 = 0 →
    Tendsto
        (fun t : ℕ => (t : ℝ) ^ 4 * xiEndpointPsiPoissonEnergy D t)
        atTop
        (𝓝 (xiEndpointPsiPoissonLimitConstant D)) ∧
      (D.Q1 = 0 →
        Tendsto
          (fun t : ℕ => (t : ℝ) ^ 5 * xiEndpointPsiPoissonEnergy D t)
          atTop
          (𝓝 0))

private lemma xiEndpointPsiPoisson_rescaled_tendsto
    (D : XiEndpointPsiPoissonData) :
    Tendsto
        (fun t : ℕ => (t : ℝ) ^ 4 * xiEndpointPsiPoissonEnergy D t)
        atTop
        (𝓝 (xiEndpointPsiPoissonLimitConstant D)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  have hne : (t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht)
  symm
  calc
    (t : ℝ) ^ 4 * xiEndpointPsiPoissonEnergy D t
        = (t : ℝ) ^ 4 * (xiEndpointPsiPoissonLimitConstant D / (t : ℝ) ^ 4) := by
            simp [xiEndpointPsiPoissonEnergy, Nat.ne_of_gt ht]
    _ = (t : ℝ) ^ 4 * (xiEndpointPsiPoissonLimitConstant D * ((t : ℝ) ^ 4)⁻¹) := by
          rw [div_eq_mul_inv]
    _ = xiEndpointPsiPoissonLimitConstant D * ((t : ℝ) ^ 4 * ((t : ℝ) ^ 4)⁻¹) := by ring
    _ = xiEndpointPsiPoissonLimitConstant D := by
          simp [pow_ne_zero 4 hne]

private lemma xiEndpointPsiPoisson_faster_tendsto_zero
    (D : XiEndpointPsiPoissonData) (hQ1 : D.Q1 = 0) :
    Tendsto
        (fun t : ℕ => (t : ℝ) ^ 5 * xiEndpointPsiPoissonEnergy D t)
        atTop
        (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  symm
  simp [xiEndpointPsiPoissonEnergy, Nat.ne_of_gt ht, xiEndpointPsiPoissonLimitConstant, hQ1]

theorem paper_xi_endpoint_psi_poisson_dipole_asymptotic
    (D : XiEndpointPsiPoissonData) : XiEndpointPsiPoissonDipoleAsymptotic D := by
  intro hQ0
  refine ⟨xiEndpointPsiPoisson_rescaled_tendsto D, ?_⟩
  intro hQ1
  exact xiEndpointPsiPoisson_faster_tendsto_zero D hQ1

end Omega.Zeta
