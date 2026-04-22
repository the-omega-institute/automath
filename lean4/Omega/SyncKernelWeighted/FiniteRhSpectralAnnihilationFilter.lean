import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators
open Polynomial

noncomputable section

def finite_rh_spectral_annihilation_filter_shift (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => a (n + 1)

def finite_rh_spectral_annihilation_filter_action (Q : Polynomial ℂ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => ∑ k ∈ Q.support, Q.coeff k * a (n + k)

def finite_rh_spectral_annihilation_filter_geometric_mode (μ : ℂ) : ℕ → ℂ :=
  fun n => μ ^ n

private lemma finite_rh_spectral_annihilation_filter_action_shift
    (a : ℕ → ℂ) (n : ℕ) :
    finite_rh_spectral_annihilation_filter_shift a n = a (n + 1) := rfl

private lemma finite_rh_spectral_annihilation_filter_action_geometric
    (Q : Polynomial ℂ) (μ : ℂ) (n : ℕ) :
    finite_rh_spectral_annihilation_filter_action Q
        (finite_rh_spectral_annihilation_filter_geometric_mode μ) n =
      Q.eval μ * μ ^ n := by
  unfold finite_rh_spectral_annihilation_filter_action
    finite_rh_spectral_annihilation_filter_geometric_mode
  calc
    ∑ k ∈ Q.support, Q.coeff k * μ ^ (n + k)
        = ∑ k ∈ Q.support, (Q.coeff k * μ ^ k) * μ ^ n := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [pow_add]
            ring
    _ = (∑ k ∈ Q.support, Q.coeff k * μ ^ k) * μ ^ n := by
          rw [← Finset.sum_mul]
    _ = Q.eval μ * μ ^ n := by
          congr 1
          simpa using (Polynomial.eval₂_eq_sum (f := RingHom.id ℂ) (x := μ) (p := Q)).symm

private lemma finite_rh_spectral_annihilation_filter_action_add
    (Q : Polynomial ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    finite_rh_spectral_annihilation_filter_action Q (fun k => a k + b k) n =
      finite_rh_spectral_annihilation_filter_action Q a n +
        finite_rh_spectral_annihilation_filter_action Q b n := by
  unfold finite_rh_spectral_annihilation_filter_action
  simp [mul_add, Finset.sum_add_distrib]

private lemma finite_rh_spectral_annihilation_filter_action_smul_mode
    (Q : Polynomial ℂ) (m μ : ℂ) (n : ℕ) :
    finite_rh_spectral_annihilation_filter_action Q (fun k => m * μ ^ k) n =
      m * (Q.eval μ * μ ^ n) := by
  unfold finite_rh_spectral_annihilation_filter_action
  calc
    ∑ k ∈ Q.support, Q.coeff k * (m * μ ^ (n + k))
        = ∑ k ∈ Q.support, m * (Q.coeff k * μ ^ (n + k)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
    _ = m * ∑ k ∈ Q.support, Q.coeff k * μ ^ (n + k) := by
          rw [Finset.mul_sum]
    _ = m * (Q.eval μ * μ ^ n) := by
          have hgeom := finite_rh_spectral_annihilation_filter_action_geometric Q μ n
          simpa [finite_rh_spectral_annihilation_filter_action,
            finite_rh_spectral_annihilation_filter_geometric_mode] using congrArg
              (fun z : ℂ => m * z) hgeom

/-- Concrete finite-spectral annihilation package: for a finite spectral sum indexed by a finite
sum of two geometric modes, the coefficient-sum model of `Q(L)` acts diagonally on each mode, and
choosing `Q(x) = (x - μ₀)(x - μ₁)` annihilates both modes exactly. -/
def finite_rh_spectral_annihilation_filter_statement : Prop :=
  ∀ (m₀ m₁ μ₀ μ₁ : ℂ) (n : ℕ),
    let a : ℕ → ℂ := fun k => m₀ * μ₀ ^ k + m₁ * μ₁ ^ k
    let Q : Polynomial ℂ := (X - C μ₀) * (X - C μ₁)
    finite_rh_spectral_annihilation_filter_shift a n = a (n + 1) ∧
    finite_rh_spectral_annihilation_filter_action Q a n = 0

/-- Paper label: `prop:finite-rh-spectral-annihilation-filter`. The direct coefficient formula for
`Q(L)` makes the action on a geometric mode immediate, and the two-mode finite spectral sum then
follows by linearity. Choosing `Q(x) = (x - μ₀)(x - μ₁)` kills both spectral modes exactly. -/
theorem paper_finite_rh_spectral_annihilation_filter :
    finite_rh_spectral_annihilation_filter_statement := by
  intro m₀ m₁ μ₀ μ₁ n
  dsimp
  refine ⟨rfl, ?_⟩
  let Q : Polynomial ℂ := (X - C μ₀) * (X - C μ₁)
  calc
    finite_rh_spectral_annihilation_filter_action Q
        (fun k => m₀ * μ₀ ^ k + m₁ * μ₁ ^ k) n
        =
          finite_rh_spectral_annihilation_filter_action Q (fun k => m₀ * μ₀ ^ k) n +
            finite_rh_spectral_annihilation_filter_action Q (fun k => m₁ * μ₁ ^ k) n := by
              rw [finite_rh_spectral_annihilation_filter_action_add]
    _ = m₀ * (Q.eval μ₀ * μ₀ ^ n) + m₁ * (Q.eval μ₁ * μ₁ ^ n) := by
          rw [finite_rh_spectral_annihilation_filter_action_smul_mode,
            finite_rh_spectral_annihilation_filter_action_smul_mode]
    _ = 0 := by
          simp [Q]

end
end Omega.SyncKernelWeighted
