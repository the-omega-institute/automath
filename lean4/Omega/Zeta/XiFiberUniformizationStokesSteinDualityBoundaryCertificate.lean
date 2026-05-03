import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for a fiber map.  The atoms are finite; `fold` records the fiber
containing each atom. -/
structure xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data where
  Atom : Type
  Fiber : Type
  [atomFintype : Fintype Atom]
  [fiberDecidableEq : DecidableEq Fiber]
  fold : Atom → Fiber

attribute [instance]
  xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data.atomFintype
  xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data.fiberDecidableEq

/-- Fiberwise coboundary: it only compares pairs in the same fiber. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_coboundary
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f : D.Atom → ℝ) (a b : D.Atom) : ℝ :=
  if D.fold a = D.fold b then f b - f a else 0

/-- The kernel predicate for the fiberwise coboundary. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kernel
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f : D.Atom → ℝ) : Prop :=
  ∀ a b : D.Atom,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_coboundary D f a b = 0

/-- Fiber-constant functions are exactly functions that factor through the fold map. -/
def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_fiberConstant
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f : D.Atom → ℝ) : Prop :=
  ∀ a b : D.Atom, D.fold a = D.fold b → f a = f b

/-- The unweighted finite inner product used by the certificate. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f g : D.Atom → ℝ) : ℝ :=
  ∑ a : D.Atom, f a * g a

/-- The corresponding squared norm. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f : D.Atom → ℝ) : ℝ :=
  xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner D f f

/-- In this finite model the signed divergence is represented by an atom function. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_delta
    (_D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (J : _D.Atom → ℝ) : _D.Atom → ℝ :=
  J

/-- The quadratic dual functional `2 <g, δJ> - ||J||²`. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (g J : D.Atom → ℝ) : ℝ :=
  2 *
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner D g
        (xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_delta D J) -
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D J

/-- Orthogonality to all fiber-constant test functions. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_orthogonal
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (g : D.Atom → ℝ) : Prop :=
  ∀ f : D.Atom → ℝ,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_fiberConstant D f →
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner D g f = 0

/-- The image of the abstract adjoint, identified with the orthogonal complement. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_adjointImage
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (g : D.Atom → ℝ) : Prop :=
  xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_orthogonal D g

/-- The KL integrand `x log x - x + 1`. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand
    (x : ℝ) : ℝ :=
  x * Real.log x - x + 1

/-- Finite KL-type defect for density ratios. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klDefect
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (r : D.Atom → ℝ) : ℝ :=
  ∑ a : D.Atom,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand (r a)

/-- Finite chi-square defect for density ratios. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_chiSquare
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (r : D.Atom → ℝ) : ℝ :=
  ∑ a : D.Atom, (r a - 1) ^ 2

lemma xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kernel_iff
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (f : D.Atom → ℝ) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kernel D f ↔
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_fiberConstant D f := by
  constructor
  · intro h a b hab
    have hzero := h a b
    have hsub : f b - f a = 0 := by
      simpa [xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_coboundary, hab]
        using hzero
    linarith
  · intro h a b
    by_cases hab : D.fold a = D.fold b
    · simp [xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_coboundary, hab,
        h a b hab]
    · simp [xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_coboundary, hab]

lemma xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue_le
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (g J : D.Atom → ℝ) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue D g J ≤
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D g := by
  classical
  have hterm : ∀ a : D.Atom, 2 * (g a * J a) - J a * J a ≤ g a * g a := by
    intro a
    nlinarith [sq_nonneg (g a - J a)]
  calc
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue D g J =
        ∑ a : D.Atom, (2 * (g a * J a) - J a * J a) := by
      simp [xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue,
        xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner,
        xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq,
        xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_delta,
        Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ a : D.Atom, g a * g a := by
      exact Finset.sum_le_sum fun a _ => hterm a
    _ = xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D g := by
      simp [xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq,
        xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner]

lemma xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue_self
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (g : D.Atom → ℝ) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue D g g =
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D g := by
  classical
  unfold xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_inner
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_delta
  let S : ℝ := ∑ a : D.Atom, g a * g a
  change 2 * S - S = S
  ring

lemma xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand_le
    {x : ℝ} (hx : 0 < x) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand x ≤
      (x - 1) ^ 2 := by
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have hmul : x * Real.log x ≤ x * (x - 1) := mul_le_mul_of_nonneg_left hlog hx.le
  unfold xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand
  nlinarith

lemma xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kl_le_chi
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data)
    (r : D.Atom → ℝ) (hr : ∀ a : D.Atom, 0 < r a) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klDefect D r ≤
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_chiSquare D r := by
  classical
  unfold xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klDefect
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_chiSquare
  exact Finset.sum_le_sum fun a _ =>
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klIntegrand_le (hr a)

/-- Concrete statement bundling the fiber kernel, adjoint image, variational norm, and
KL--chi-square boundary certificate. -/
noncomputable def xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_statement
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data) : Prop :=
  (∀ f : D.Atom → ℝ,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kernel D f ↔
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_fiberConstant D f) ∧
  (∀ g : D.Atom → ℝ,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_adjointImage D g ↔
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_orthogonal D g) ∧
  (∀ g J : D.Atom → ℝ,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue D g J ≤
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D g) ∧
  (∀ g : D.Atom → ℝ,
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue D g g =
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_normSq D g) ∧
  (∀ r : D.Atom → ℝ, (∀ a : D.Atom, 0 < r a) →
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_klDefect D r ≤
      xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_chiSquare D r)

/-- Paper label: `prop:xi-fiber-uniformization-stokes-stein-duality-boundary-certificate`. -/
theorem paper_xi_fiber_uniformization_stokes_stein_duality_boundary_certificate
    (D : xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_data) :
    xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kernel_iff D
  · intro g
    rfl
  · exact xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue_le D
  · exact xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_dualValue_self D
  · exact xi_fiber_uniformization_stokes_stein_duality_boundary_certificate_kl_le_chi D

end Omega.Zeta
