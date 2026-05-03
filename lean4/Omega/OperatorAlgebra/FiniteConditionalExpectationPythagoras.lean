import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Concrete finite-fiber probability data for the conditional-expectation Pythagoras identity. -/
structure finite_condexp_pythagoras_data where
  X : Type
  instFintypeX : Fintype X
  Y : X → Type
  instFintypeY : ∀ x, Fintype (Y x)
  μ : Sigma Y → ℚ
  μ_nonneg : ∀ z, 0 ≤ μ z
  fiberMass_pos :
    ∀ x,
      0 <
        letI := instFintypeY x
        ∑ y : Y x, μ ⟨x, y⟩

attribute [instance] finite_condexp_pythagoras_data.instFintypeX
attribute [instance] finite_condexp_pythagoras_data.instFintypeY

namespace finite_condexp_pythagoras_data

/-- Total mass of one finite fiber. -/
def finite_condexp_pythagoras_fiberMass (D : finite_condexp_pythagoras_data) (x : D.X) : ℚ :=
  letI := D.instFintypeY x
  ∑ y : D.Y x, D.μ ⟨x, y⟩

/-- Weighted fiber average, i.e. the finite conditional expectation on a displayed fiber. -/
def finite_condexp_pythagoras_condexp
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) : Sigma D.Y → ℚ
  | ⟨x, _y⟩ =>
      letI := D.instFintypeY x
      (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩) /
        D.finite_condexp_pythagoras_fiberMass x

/-- Weighted finite inner product, written fiber-by-fiber. -/
def finite_condexp_pythagoras_inner
    (D : finite_condexp_pythagoras_data) (f g : Sigma D.Y → ℚ) : ℚ :=
  letI := D.instFintypeX
  ∑ x : D.X,
    letI := D.instFintypeY x
    ∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩ * g ⟨x, y⟩

/-- Weighted squared `L^2` norm. -/
def finite_condexp_pythagoras_normSq
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) : ℚ :=
  D.finite_condexp_pythagoras_inner f f

lemma finite_condexp_pythagoras_fiberMass_pos
    (D : finite_condexp_pythagoras_data) (x : D.X) :
    0 < D.finite_condexp_pythagoras_fiberMass x := by
  simpa [finite_condexp_pythagoras_fiberMass] using D.fiberMass_pos x

lemma finite_condexp_pythagoras_fiberMass_ne_zero
    (D : finite_condexp_pythagoras_data) (x : D.X) :
    D.finite_condexp_pythagoras_fiberMass x ≠ 0 :=
  (D.finite_condexp_pythagoras_fiberMass_pos x).ne'

lemma finite_condexp_pythagoras_residual_fiber_sum
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) (x : D.X) :
    letI := D.instFintypeY x
    ∑ y : D.Y x,
      D.μ ⟨x, y⟩ *
        (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) = 0 := by
  classical
  letI := D.instFintypeY x
  set S : ℚ := ∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩
  set M : ℚ := D.finite_condexp_pythagoras_fiberMass x
  have hM : M ≠ 0 := by
    simpa [M] using D.finite_condexp_pythagoras_fiberMass_ne_zero x
  have hsplit :
      (∑ y : D.Y x,
        D.μ ⟨x, y⟩ *
          (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩)) =
        S - (S / M) * M := by
    simp [S, M, finite_condexp_pythagoras_condexp, finite_condexp_pythagoras_fiberMass,
      mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, div_eq_mul_inv, mul_comm]
  rw [hsplit]
  field_simp [hM]
  ring

lemma finite_condexp_pythagoras_fiber_identity
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) (x : D.X) :
    letI := D.instFintypeY x
    (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩ * f ⟨x, y⟩) =
      (∑ y : D.Y x,
        D.μ ⟨x, y⟩ *
          D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ *
          D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) +
        (∑ y : D.Y x,
          D.μ ⟨x, y⟩ *
            (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) *
            (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩)) := by
  classical
  letI := D.instFintypeY x
  set E : ℚ :=
    (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩) /
      D.finite_condexp_pythagoras_fiberMass x
  have hE (y : D.Y x) : D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ = E := by
    simp [E, finite_condexp_pythagoras_condexp]
  have hzero :
      (∑ y : D.Y x, D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - E)) = 0 := by
    simpa [hE] using D.finite_condexp_pythagoras_residual_fiber_sum f x
  calc
    (∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩ * f ⟨x, y⟩)
        = Finset.sum Finset.univ (fun y : D.Y x =>
            (D.μ ⟨x, y⟩ * E * E) +
              (D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - E) * (f ⟨x, y⟩ - E)) +
                (2 * E) * (D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - E))) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          ring_nf
    _ =
        (∑ y : D.Y x, D.μ ⟨x, y⟩ * E * E) +
          (∑ y : D.Y x,
            D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - E) * (f ⟨x, y⟩ - E)) +
            (2 * E) * (∑ y : D.Y x, D.μ ⟨x, y⟩ * (f ⟨x, y⟩ - E)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ =
        (∑ y : D.Y x, D.μ ⟨x, y⟩ *
          D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ *
          D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) +
          (∑ y : D.Y x,
            D.μ ⟨x, y⟩ *
              (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) *
              (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩)) := by
          rw [hzero]
          simp [hE]

lemma finite_condexp_pythagoras_normSq_nonneg
    (D : finite_condexp_pythagoras_data) (f : Sigma D.Y → ℚ) :
    0 ≤ D.finite_condexp_pythagoras_normSq f := by
  classical
  simp [finite_condexp_pythagoras_normSq, finite_condexp_pythagoras_inner]
  exact Finset.sum_nonneg fun x _hx =>
    Finset.sum_nonneg fun y _hy => by
      simpa [mul_assoc] using
        mul_nonneg (D.μ_nonneg ⟨x, y⟩) (mul_self_nonneg (f ⟨x, y⟩))

end finite_condexp_pythagoras_data

open finite_condexp_pythagoras_data

/-- The finite conditional-expectation Pythagoras statement for the concrete displayed fibers. -/
def finite_condexp_pythagoras_statement (D : finite_condexp_pythagoras_data) : Prop :=
  ∀ f : Sigma D.Y → ℚ,
    D.finite_condexp_pythagoras_normSq f =
        D.finite_condexp_pythagoras_normSq (D.finite_condexp_pythagoras_condexp f) +
          D.finite_condexp_pythagoras_normSq
            (fun z => f z - D.finite_condexp_pythagoras_condexp f z) ∧
      D.finite_condexp_pythagoras_normSq (D.finite_condexp_pythagoras_condexp f) ≤
        D.finite_condexp_pythagoras_normSq f

/-- Paper label: `thm:finite-condexp-pythagoras`. -/
theorem paper_finite_condexp_pythagoras (D : finite_condexp_pythagoras_data) :
    finite_condexp_pythagoras_statement D := by
  classical
  intro f
  letI := D.instFintypeX
  have hidentity :
      D.finite_condexp_pythagoras_normSq f =
        D.finite_condexp_pythagoras_normSq (D.finite_condexp_pythagoras_condexp f) +
          D.finite_condexp_pythagoras_normSq
            (fun z => f z - D.finite_condexp_pythagoras_condexp f z) := by
    simp [finite_condexp_pythagoras_normSq, finite_condexp_pythagoras_inner]
    calc
      (∑ x : D.X, ∑ y : D.Y x, D.μ ⟨x, y⟩ * f ⟨x, y⟩ * f ⟨x, y⟩)
          =
            ∑ x : D.X,
              ((∑ y : D.Y x,
                D.μ ⟨x, y⟩ *
                  D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ *
                  D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) +
                (∑ y : D.Y x,
                  D.μ ⟨x, y⟩ *
                    (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) *
                    (f ⟨x, y⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, y⟩))) := by
              exact Finset.sum_congr rfl fun x _hx =>
                D.finite_condexp_pythagoras_fiber_identity f x
      _ =
          (∑ x : D.X, ∑ y : D.Y x,
            D.μ ⟨x, y⟩ *
              D.finite_condexp_pythagoras_condexp f ⟨x, y⟩ *
              D.finite_condexp_pythagoras_condexp f ⟨x, y⟩) +
            ∑ x : D.X, ∑ x_1 : D.Y x,
              D.μ ⟨x, x_1⟩ *
                (f ⟨x, x_1⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, x_1⟩) *
                (f ⟨x, x_1⟩ - D.finite_condexp_pythagoras_condexp f ⟨x, x_1⟩) := by
              rw [Finset.sum_add_distrib]
  refine ⟨hidentity, ?_⟩
  have hnonneg :
      0 ≤
        D.finite_condexp_pythagoras_normSq
          (fun z => f z - D.finite_condexp_pythagoras_condexp f z) :=
    D.finite_condexp_pythagoras_normSq_nonneg
      (fun z => f z - D.finite_condexp_pythagoras_condexp f z)
  linarith

end Omega.OperatorAlgebra
