import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.POM.FiberReflector

open Finset
open scoped BigOperators

section FiberReflector

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The finite fiber of `P` over `x`, viewed as a filtered subset of `Ω`. -/
def fiberSet (P : Ω → X) (x : X) : Finset Ω :=
  Finset.univ.filter fun ω => P ω = x

/-- Cardinality of the fiber over `x`. -/
def fiberCard (P : Ω → X) (x : X) : ℕ :=
  (fiberSet P x).card

/-- Push a scalar-valued function on `Ω` forward along `P` by summing on each fiber. -/
def pushforward (P : Ω → X) (μ : Ω → ℚ) : X → ℚ :=
  fun x => Finset.sum (fiberSet P x) μ

/-- Lift a function on `X` back to `Ω` by distributing its mass uniformly on each fiber. -/
def uniformLift (P : Ω → X) (π : X → ℚ) : Ω → ℚ :=
  fun ω => π (P ω) / fiberCard P (P ω)

/-- The reflector `K = Q ∘ P` obtained from pushforward and fiber-uniform lift. -/
def reflector (P : Ω → X) (μ : Ω → ℚ) : Ω → ℚ :=
  uniformLift P (pushforward P μ)

/-- A scalar field on `Ω` is fiberwise uniform if it is constant on the fibers of `P`. -/
def FiberwiseUniform (P : Ω → X) (μ : Ω → ℚ) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, P ω₁ = P ω₂ → μ ω₁ = μ ω₂

/-- Idempotence of the reflector `K`. -/
def reflectorIdempotent (P : Ω → X) : Prop :=
  ∀ μ : Ω → ℚ, reflector P (reflector P μ) = reflector P μ

/-- The formula `K μ = Q (P μ)`. -/
def uniformLiftFormula (P : Ω → X) : Prop :=
  ∀ μ : Ω → ℚ, reflector P μ = uniformLift P (pushforward P μ)

/-- Fixed points of `K` are exactly the fiberwise-uniform functions. -/
def fixedPointCharacterization (P : Ω → X) : Prop :=
  ∀ μ : Ω → ℚ, reflector P μ = μ ↔ FiberwiseUniform P μ

private lemma fiberCard_pos_of_mem (P : Ω → X) (ω : Ω) :
    0 < fiberCard P (P ω) := by
  unfold fiberCard fiberSet
  refine Finset.card_pos.mpr ?_
  exact ⟨ω, by simp⟩

private lemma fiberCard_ne_zero (P : Ω → X) (hP : Function.Surjective P) (x : X) :
    (fiberCard P x : ℚ) ≠ 0 := by
  have hpos : 0 < fiberCard P x := by
    rcases hP x with ⟨ω, rfl⟩
    exact fiberCard_pos_of_mem P ω
  exact_mod_cast Nat.ne_of_gt hpos

private lemma pushforward_uniformLift (P : Ω → X) (hP : Function.Surjective P) (π : X → ℚ) :
    pushforward P (uniformLift P π) = π := by
  funext x
  have hc : (fiberCard P x : ℚ) ≠ 0 := fiberCard_ne_zero P hP x
  unfold pushforward uniformLift
  calc
    Finset.sum (fiberSet P x) (fun ω => π (P ω) / fiberCard P (P ω))
        = Finset.sum (fiberSet P x) (fun _ => π x / fiberCard P x) := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            have hωx : P ω = x := by
              exact (Finset.mem_filter.mp hω).2
            simp [hωx, fiberCard]
    _ = (fiberCard P x : ℚ) * (π x / fiberCard P x) := by
          simp [fiberCard, fiberSet]
    _ = π x := by
          rw [div_eq_mul_inv]
          calc
            (fiberCard P x : ℚ) * (π x * (fiberCard P x : ℚ)⁻¹)
                = π x * ((fiberCard P x : ℚ) * (fiberCard P x : ℚ)⁻¹) := by ring
            _ = π x := by simp [hc]

private lemma reflector_eq_self_of_fiberwiseUniform (P : Ω → X) (μ : Ω → ℚ)
    (hμ : FiberwiseUniform P μ) :
    reflector P μ = μ := by
  funext ω
  have hc : (fiberCard P (P ω) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fiberCard_pos_of_mem P ω)
  have hsum :
      Finset.sum (fiberSet P (P ω)) μ = (fiberCard P (P ω) : ℚ) * μ ω := by
    calc
      Finset.sum (fiberSet P (P ω)) μ = Finset.sum (fiberSet P (P ω)) (fun _ => μ ω) := by
        refine Finset.sum_congr rfl ?_
        intro ω' hω'
        exact hμ (Finset.mem_filter.mp hω').2
      _ = (fiberCard P (P ω) : ℚ) * μ ω := by
            simp [fiberCard, fiberSet]
  unfold reflector uniformLift pushforward
  rw [hsum]
  rw [div_eq_mul_inv]
  calc
    (fiberCard P (P ω) : ℚ) * μ ω * (fiberCard P (P ω) : ℚ)⁻¹
        = μ ω * ((fiberCard P (P ω) : ℚ) * (fiberCard P (P ω) : ℚ)⁻¹) := by ring
    _ = μ ω := by simp [hc]

private lemma fiberwiseUniform_of_reflector_eq_self (P : Ω → X) (μ : Ω → ℚ)
    (hfix : reflector P μ = μ) :
    FiberwiseUniform P μ := by
  intro ω₁ ω₂ hω
  have h₁ : reflector P μ ω₁ = μ ω₁ := by
    simpa using congrFun hfix ω₁
  have h₂ : reflector P μ ω₂ = μ ω₂ := by
    simpa using congrFun hfix ω₂
  calc
    μ ω₁ = reflector P μ ω₁ := h₁.symm
    _ = reflector P μ ω₂ := by
          unfold reflector uniformLift pushforward
          simp [hω, fiberCard, fiberSet]
    _ = μ ω₂ := h₂

/-- Fiber reflector: `K = Q ∘ P` is idempotent, computes the fiber-uniform lift, and its fixed
points are exactly the fiberwise-uniform functions.
    thm:pom-fiber-reflector -/
theorem paper_pom_fiber_reflector (P : Ω → X) (hP : Function.Surjective P) :
    reflectorIdempotent P ∧ uniformLiftFormula P ∧ fixedPointCharacterization P := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    unfold reflector
    rw [pushforward_uniformLift P hP (pushforward P μ)]
  · intro μ
    rfl
  · intro μ
    constructor
    · exact fiberwiseUniform_of_reflector_eq_self P μ
    · exact reflector_eq_self_of_fiberwiseUniform P μ

end FiberReflector

end Omega.POM.FiberReflector
