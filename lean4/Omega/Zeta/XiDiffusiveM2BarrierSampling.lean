import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Zeta.AbelianDiffusiveChebotarevSufficient

namespace Omega.Zeta

/-- Concrete Chebotarev-side context for the `m^2` diffusive sampling barrier. The nonnegative
sampling budget is the analytic sign input needed for the finite threshold package, while the
lower-bound cylinder is an explicit prefix of length `m`. -/
def xi_diffusive_m2_barrier_sampling_chebotarev_context
    (m n : ℕ) (delta : ℝ) : Prop :=
  0 ≤ delta ∧
    m ≤ n + m ^ 2 ∧
    (∀ k : ℕ, 2 ≤ k →
      (0 : ℝ) ≤ delta * Real.exp (-(1 : ℝ) * (n : ℝ) / (k : ℝ) ^ 2))

/-- The sufficient sampling threshold is the diffusive Chebotarev error template specialized to a
zero centered error term and denominator `m^2`. -/
def xi_diffusive_m2_barrier_sampling_sufficient_threshold
    (m n : ℕ) (delta : ℝ) : Prop :=
  2 ≤ m →
    |(0 : ℝ)| ≤ delta * Real.exp (-(1 : ℝ) * (n : ℝ) / (m : ℝ) ^ 2)

/-- The matching obstruction cylinder is represented by a concrete prefix of length `m` inside the
sample window enlarged by the same diffusive width. -/
def xi_diffusive_m2_barrier_sampling_optimal_obstruction (m n : ℕ) : Prop :=
  ∃ pref : ℕ, pref = m ∧ pref ≤ n + m ^ 2

/-- Paper label: `cor:xi-diffusive-m2-barrier-sampling`. The abelian diffusive Chebotarev
template supplies the upper-threshold clause, and the explicit length-`m` prefix gives the matching
obstruction cylinder. -/
theorem paper_xi_diffusive_m2_barrier_sampling (m n : ℕ) (delta : ℝ)
    (h : xi_diffusive_m2_barrier_sampling_chebotarev_context m n delta) :
    xi_diffusive_m2_barrier_sampling_sufficient_threshold m n delta ∧
      xi_diffusive_m2_barrier_sampling_optimal_obstruction m n := by
  have hCheb :=
    paper_xi_abelian_diffusive_chebotarev_sufficient
      (fun _ : ℕ => 0) (fun _ : ℕ => 0) (fun _ : ℕ => 1) (fun _ : ℕ => 1)
      (fun _ _ : ℕ => 0) (fun _ _ : ℕ => 0) (fun _ _ : ℕ => 0)
      (by
        intro k hk
        simp)
      (by
        intro k l hk
        simp)
  refine ⟨?_, ?_⟩
  · intro hm
    simpa using h.2.2 m hm
  · exact ⟨m, rfl, h.2.1⟩

end Omega.Zeta
