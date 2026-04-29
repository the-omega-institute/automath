import Omega.OperatorAlgebra.FiniteConditionalExpectationPythagoras

open scoped BigOperators

namespace Omega.OperatorAlgebra

open finite_condexp_pythagoras_data

/-- Weighted global mean for the finite displayed-fiber conditional-expectation data. -/
def finite_condexp_variance_decomposition_mean
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) : ℚ :=
  letI := D.instFintypeX
  ∑ x : D.X, by
    letI := D.instFintypeY x
    exact ∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩

/-- Weighted finite variance around the global mean. -/
def finite_condexp_variance_decomposition_variance
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) : ℚ :=
  D.finite_condexp_pythagoras_normSq
    (fun z => f z - finite_condexp_variance_decomposition_mean D f)

/-- Fiberwise variance defect, equivalently the squared residual after conditional expectation. -/
def finite_condexp_variance_decomposition_defect
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) : ℚ :=
  D.finite_condexp_pythagoras_normSq
    (fun z => f z - D.finite_condexp_pythagoras_condexp f z)

lemma finite_condexp_variance_decomposition_condexp_mean
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) :
    finite_condexp_variance_decomposition_mean D
        (D.finite_condexp_pythagoras_condexp f) =
      finite_condexp_variance_decomposition_mean D f := by
  classical
  letI := D.instFintypeX
  unfold finite_condexp_variance_decomposition_mean
  refine Finset.sum_congr rfl ?_
  intro x _hx
  letI := D.instFintypeY x
  have hres := D.finite_condexp_pythagoras_residual_fiber_sum f x
  have hdiff :
      (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩) -
        (∑ y : D.Y x,
          D.μ ⟨x, y⟩ * D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) = 0 := by
    simpa [mul_sub, Finset.sum_sub_distrib] using hres
  linarith

lemma finite_condexp_variance_decomposition_condexp_centered
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) :
    D.finite_condexp_pythagoras_condexp
        (fun z => f z - finite_condexp_variance_decomposition_mean D f) =
      fun z =>
        D.finite_condexp_pythagoras_condexp f z -
          finite_condexp_variance_decomposition_mean D f := by
  classical
  funext z
  rcases z with ⟨x, y⟩
  letI := D.instFintypeY x
  set S : ℚ := ∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩
  set M : ℚ := D.finite_condexp_pythagoras_fiberMass x
  set c : ℚ := finite_condexp_variance_decomposition_mean D f
  have hM : M ≠ 0 := by
    simpa [M] using D.finite_condexp_pythagoras_fiberMass_ne_zero x
  have hM' : D.finite_condexp_pythagoras_fiberMass x ≠ 0 :=
    D.finite_condexp_pythagoras_fiberMass_ne_zero x
  have hsum :
      (∑ y : D.Y x, D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - c)) = S - c * M := by
    calc
      (∑ y : D.Y x, D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - c))
          = ∑ y : D.Y x, (D.μ ⟨x, y⟩ * f ⟨x, y⟩ - c * D.μ ⟨x, y⟩) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            ring
      _ = (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩) -
            ∑ y : D.Y x, c * D.μ ⟨x, y⟩ := by
            rw [Finset.sum_sub_distrib]
      _ = S - c * M := by
            simp [S, M, finite_condexp_pythagoras_fiberMass, Finset.mul_sum]
  simp [finite_condexp_pythagoras_condexp, S, M, c, hsum]
  field_simp [hM, hM']

lemma finite_condexp_variance_decomposition_condexp_idempotent
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) :
    D.finite_condexp_pythagoras_condexp (D.finite_condexp_pythagoras_condexp f) =
      D.finite_condexp_pythagoras_condexp f := by
  classical
  funext z
  rcases z with ⟨x, y⟩
  letI := D.instFintypeY x
  set M : ℚ := D.finite_condexp_pythagoras_fiberMass x
  have hM : M ≠ 0 := by
    simpa [M] using D.finite_condexp_pythagoras_fiberMass_ne_zero x
  set E : ℚ := D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ with hE
  have hconst (y' : D.Y x) :
      D.finite_condexp_pythagoras_condexp f ⟨x, y'⟩ = E := by
    simp [E, finite_condexp_pythagoras_condexp]
  calc
    D.finite_condexp_pythagoras_condexp (D.finite_condexp_pythagoras_condexp f) ⟨x, y⟩
        =
          (∑ y' : D.Y x,
            D.μ ⟨x, y'⟩ * D.finite_condexp_pythagoras_condexp f ⟨x, y'⟩) / M := by
          simp [M, finite_condexp_pythagoras_condexp]
    _ = (∑ y' : D.Y x, D.μ ⟨x, y'⟩ * E) / M := by
          simp [hconst]
    _ = ((∑ y' : D.Y x, D.μ ⟨x, y'⟩) * E) / M := by
          rw [Finset.sum_mul]
    _ = (M * E) / M := by
          simp [M, finite_condexp_pythagoras_fiberMass]
    _ = E := by
          field_simp [hM]
    _ = D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ := by
          rw [hE]

/-- The finite conditional-expectation variance decomposition over concrete displayed fibers. -/
def finite_condexp_variance_decomposition_statement
    (D : finite_condexp_pythagoras_data) : Prop :=
  ∀ f : Sigma D.Y → ℚ,
    finite_condexp_variance_decomposition_defect D f =
        D.finite_condexp_pythagoras_normSq
          (fun z => f z - D.finite_condexp_pythagoras_condexp f z) ∧
      finite_condexp_variance_decomposition_variance D f =
        finite_condexp_variance_decomposition_variance D
            (D.finite_condexp_pythagoras_condexp f) +
          finite_condexp_variance_decomposition_defect D f ∧
      finite_condexp_variance_decomposition_defect D
          (D.finite_condexp_pythagoras_condexp f) = 0 ∧
        finite_condexp_variance_decomposition_defect D
            (D.finite_condexp_pythagoras_condexp f) ≤
          finite_condexp_variance_decomposition_defect D f

/-- Paper label: `cor:finite-condexp-variance-decomposition`. -/
theorem paper_finite_condexp_variance_decomposition (D : finite_condexp_pythagoras_data) :
    finite_condexp_variance_decomposition_statement D := by
  classical
  intro f
  let centered : Sigma D.Y → ℚ :=
    fun z => f z - finite_condexp_variance_decomposition_mean D f
  have hpyth := paper_finite_condexp_pythagoras D centered
  have hcenter :
      D.finite_condexp_pythagoras_condexp centered =
        fun z =>
          D.finite_condexp_pythagoras_condexp f z -
            finite_condexp_variance_decomposition_mean D f := by
    simpa [centered] using finite_condexp_variance_decomposition_condexp_centered D f
  have hmean :
      finite_condexp_variance_decomposition_mean D
          (D.finite_condexp_pythagoras_condexp f) =
        finite_condexp_variance_decomposition_mean D f :=
    finite_condexp_variance_decomposition_condexp_mean D f
  have hvariance :
      finite_condexp_variance_decomposition_variance D f =
        finite_condexp_variance_decomposition_variance D
            (D.finite_condexp_pythagoras_condexp f) +
          finite_condexp_variance_decomposition_defect D f := by
    rw [finite_condexp_variance_decomposition_variance,
      finite_condexp_variance_decomposition_variance,
      finite_condexp_variance_decomposition_defect]
    calc
      D.finite_condexp_pythagoras_normSq
          (fun z => f z - finite_condexp_variance_decomposition_mean D f)
          =
            D.finite_condexp_pythagoras_normSq
              (D.finite_condexp_pythagoras_condexp centered) +
              D.finite_condexp_pythagoras_normSq
                (fun z => centered z -
                  D.finite_condexp_pythagoras_condexp centered z) := hpyth.1
      _ =
            D.finite_condexp_pythagoras_normSq
              (fun z =>
                D.finite_condexp_pythagoras_condexp f z -
                  finite_condexp_variance_decomposition_mean D
                    (D.finite_condexp_pythagoras_condexp f)) +
              D.finite_condexp_pythagoras_normSq
                (fun z => f z - D.finite_condexp_pythagoras_condexp f z) := by
          congr 2
          · rw [hcenter]
            funext z
            rw [hmean]
          · rw [hcenter]
            funext z
            simp [centered]
  have hzero :
      finite_condexp_variance_decomposition_defect D
          (D.finite_condexp_pythagoras_condexp f) = 0 := by
    rw [finite_condexp_variance_decomposition_defect,
      finite_condexp_variance_decomposition_condexp_idempotent D f]
    simp [finite_condexp_pythagoras_normSq, finite_condexp_pythagoras_inner]
  refine ⟨rfl, hvariance, hzero, ?_⟩
  rw [hzero]
  exact D.finite_condexp_pythagoras_normSq_nonneg
    (fun z => f z - D.finite_condexp_pythagoras_condexp f z)

end Omega.OperatorAlgebra
