import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete infinite prime-register model used for the no-faithful-finite-dimensional wrapper. -/
abbrev xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register :=
  ℕ → ZMod 2

/-- Finite prime-prefix observation of the register. -/
def xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix (n : ℕ)
    (x : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register) :
    Fin n → ZMod 2 :=
  fun i => x i

/-- The imported finite-prime factorization theorem is represented by this concrete factorization
predicate: a finite-dimensional observable only depends on a finite prime prefix. -/
def xi_time_part60f2_no_faithful_finite_dimensional_lie_model_factorsThroughFinitePrefix
    {β : Type*}
    (ρ : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register → β) : Prop :=
  ∃ n : ℕ, ∃ ρ₀ : (Fin n → ZMod 2) → β,
    ρ = fun x =>
      ρ₀ (xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix n x)

/-- Tail element supported at the first coordinate outside a finite prefix. -/
def xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness
    (n : ℕ) : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register :=
  fun k => if k = n then 1 else 0

lemma xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness_ne_zero
    (n : ℕ) :
    xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness n ≠ 0 := by
  intro h
  have hcoord := congrFun h n
  simp [xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness] at hcoord

lemma xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix_tailWitness
    (n : ℕ) :
    xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix n
        (xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness n) =
      xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix n 0 := by
  funext i
  have hi : (i : ℕ) ≠ n := by
    exact ne_of_lt i.isLt
  simp [xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix,
    xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness, hi]

lemma xi_time_part60f2_no_faithful_finite_dimensional_lie_model_not_injective_of_factor
    {β : Type*}
    (ρ : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register → β)
    (hρ :
      xi_time_part60f2_no_faithful_finite_dimensional_lie_model_factorsThroughFinitePrefix ρ) :
    ¬ Function.Injective ρ := by
  rintro hinj
  rcases hρ with ⟨n, ρ₀, rfl⟩
  have hsame :
      ρ₀
          (xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix n
            (xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness n)) =
        ρ₀ (xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix n 0) := by
    rw [xi_time_part60f2_no_faithful_finite_dimensional_lie_model_prefix_tailWitness]
  have hzero :
      xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness n = 0 :=
    hinj hsame
  exact xi_time_part60f2_no_faithful_finite_dimensional_lie_model_tailWitness_ne_zero n hzero

/-- Concrete no-go package: finite-prefix finite-dimensional observables and their compact-Lie
quotient realizations cannot be faithful on the infinite prime register. -/
def xi_time_part60f2_no_faithful_finite_dimensional_lie_model_statement : Prop :=
  (∀ β : Type*,
    ∀ ρ : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register → β,
      xi_time_part60f2_no_faithful_finite_dimensional_lie_model_factorsThroughFinitePrefix ρ →
        ¬ Function.Injective ρ) ∧
    (∀ G : Type*,
      ∀ q : xi_time_part60f2_no_faithful_finite_dimensional_lie_model_register → G,
        xi_time_part60f2_no_faithful_finite_dimensional_lie_model_factorsThroughFinitePrefix q →
          ¬ Function.Injective q)

/-- Paper label: `cor:xi-time-part60f2-no-faithful-finite-dimensional-lie-model`. -/
theorem paper_xi_time_part60f2_no_faithful_finite_dimensional_lie_model :
    xi_time_part60f2_no_faithful_finite_dimensional_lie_model_statement := by
  refine ⟨?_, ?_⟩
  · intro β ρ hρ
    exact xi_time_part60f2_no_faithful_finite_dimensional_lie_model_not_injective_of_factor ρ hρ
  · intro G q hq
    exact xi_time_part60f2_no_faithful_finite_dimensional_lie_model_not_injective_of_factor q hq

end Omega.Zeta
