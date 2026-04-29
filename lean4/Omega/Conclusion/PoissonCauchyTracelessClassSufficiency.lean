import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- A symmetric covariance matrix encoded by its `(γγ, γδ, δδ)` entries. -/
def conclusion_poisson_cauchy_traceless_class_sufficiency_covariance := ℝ × ℝ × ℝ

/-- The traceless covariance class, written in the two coordinates `(γγ - δδ, γδ)`. -/
def conclusion_poisson_cauchy_traceless_class_sufficiency_class
    (S : conclusion_poisson_cauchy_traceless_class_sufficiency_covariance) : ℝ × ℝ :=
  (S.1 - S.2.2, S.2.1)

/-- The second-order fingerprint constants determined by a traceless covariance class:
raw KL, Fisher, projected KL, and the two drift coordinates. -/
def conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint
    (S : conclusion_poisson_cauchy_traceless_class_sufficiency_covariance) :
    ℝ × ℝ × ℝ × (ℝ × ℝ) :=
  let A := (conclusion_poisson_cauchy_traceless_class_sufficiency_class S).1
  let B := (conclusion_poisson_cauchy_traceless_class_sufficiency_class S).2
  (A ^ 2 / 8 + B ^ 2 / 2, A ^ 2 / 2 + 2 * B ^ 2, A ^ 2 / 16 + B ^ 2 / 4, (A, B))

/-- Adding the same scalar variance to both diagonal entries of a covariance matrix. -/
def conclusion_poisson_cauchy_traceless_class_sufficiency_scalar_shift
    (S : conclusion_poisson_cauchy_traceless_class_sufficiency_covariance) (s : ℝ) :
    conclusion_poisson_cauchy_traceless_class_sufficiency_covariance :=
  (S.1 + s, S.2.1, S.2.2 + s)

/-- Paper label: `thm:conclusion-poisson-cauchy-traceless-class-sufficiency`.
The second-order fingerprint factors through the traceless covariance class, hence scalar
diagonal shifts leave the whole fingerprint unchanged. -/
def conclusion_poisson_cauchy_traceless_class_sufficiency_statement : Prop :=
  (∀ S S' : conclusion_poisson_cauchy_traceless_class_sufficiency_covariance,
      conclusion_poisson_cauchy_traceless_class_sufficiency_class S' =
          conclusion_poisson_cauchy_traceless_class_sufficiency_class S →
        conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint S' =
          conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint S) ∧
    ∀ (S : conclusion_poisson_cauchy_traceless_class_sufficiency_covariance) (s : ℝ),
      conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint
          (conclusion_poisson_cauchy_traceless_class_sufficiency_scalar_shift S s) =
        conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint S

theorem paper_conclusion_poisson_cauchy_traceless_class_sufficiency :
    conclusion_poisson_cauchy_traceless_class_sufficiency_statement := by
  constructor
  · intro S S' hclass
    simp [conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint, hclass]
  · intro S s
    simp [conclusion_poisson_cauchy_traceless_class_sufficiency_fingerprint,
      conclusion_poisson_cauchy_traceless_class_sufficiency_class,
      conclusion_poisson_cauchy_traceless_class_sufficiency_scalar_shift]

end
end Omega.Conclusion
