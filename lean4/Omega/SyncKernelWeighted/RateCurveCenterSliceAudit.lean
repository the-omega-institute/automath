import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The explicit center-slice polynomial `Q(u)` used in the audited factorization
`R(1/2, u) = -(u - 1)^6 Q(u) / 64`. -/
def rateCenterQ (u : ℚ) : ℚ :=
  16 * (u ^ 2 + 1) ^ 8

/-- The same center-slice polynomial viewed over `ℝ`. -/
def rateCenterQReal (u : ℝ) : ℝ :=
  16 * (u ^ 2 + 1) ^ 8

/-- Self-reciprocal identity for the center-slice polynomial. -/
def rateCenterQReciprocalIdentity : Prop :=
  ∀ u : ℚ, u ≠ 0 → rateCenterQ u = u ^ 16 * rateCenterQ u⁻¹

/-- The audited center-slice polynomial has no real roots. -/
def rateCenterQNoRealRoots : Prop :=
  ∀ u : ℝ, rateCenterQReal u ≠ 0

/-- Positivity of the center-slice polynomial on the real axis. -/
def rateCenterQPositiveOnReals : Prop :=
  ∀ u : ℝ, 0 < rateCenterQReal u

private theorem rateCenterQ_positive (u : ℝ) : 0 < rateCenterQReal u := by
  have hsq : 0 ≤ u ^ 2 := by positivity
  have hbase : 0 < u ^ 2 + 1 := by nlinarith
  have hpow : 0 < (u ^ 2 + 1) ^ 8 := by positivity
  dsimp [rateCenterQReal]
  positivity

/-- Center-slice reciprocal identity, absence of real roots, and positivity on the real axis.
    prop:rate-center-Q-reciprocal-no-real -/
theorem paper_rate_center_q_reciprocal_no_real :
    rateCenterQReciprocalIdentity ∧ rateCenterQNoRealRoots ∧ rateCenterQPositiveOnReals := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    dsimp [rateCenterQ]
    field_simp [hu]
    ring
  · intro u
    exact (rateCenterQ_positive u).ne'
  · exact rateCenterQ_positive

end Omega.SyncKernelWeighted
