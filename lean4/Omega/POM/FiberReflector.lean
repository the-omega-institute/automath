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

/-- The kernel entry of the fiber reflector. -/
def kmKernel (P : Ω → X) (ω ω' : Ω) : ℚ :=
  if P ω = P ω' then 1 / fiberCard P (P ω) else 0

/-- The fiber-reflector kernel is symmetric, doubly stochastic, idempotent, and acts by
fiberwise averaging. -/
def kmBistochastic (P : Ω → X) : Prop :=
  (∀ ω ω' : Ω, kmKernel P ω ω' = kmKernel P ω' ω) ∧
    (∀ ω : Ω, Finset.sum Finset.univ (fun ω' => kmKernel P ω ω') = 1) ∧
    (∀ ω' : Ω, Finset.sum Finset.univ (fun ω => kmKernel P ω ω') = 1) ∧
    (∀ ω ω' : Ω,
      Finset.sum Finset.univ (fun η => kmKernel P ω η * kmKernel P η ω') = kmKernel P ω ω') ∧
    (∀ μ : Ω → ℚ, ∀ ω : Ω,
      reflector P μ ω = Finset.sum Finset.univ (fun ω' => kmKernel P ω ω' * μ ω'))

private def deltaMass (ω₀ : Ω) : Ω → ℚ :=
  fun ω => if ω = ω₀ then 1 else 0

private lemma kmKernel_symm (P : Ω → X) (ω ω' : Ω) :
    kmKernel P ω ω' = kmKernel P ω' ω := by
  by_cases h : P ω = P ω'
  · unfold kmKernel
    rw [if_pos h, if_pos h.symm]
    simp [h]
  · have h' : P ω' ≠ P ω := fun h'' => h h''.symm
    unfold kmKernel
    rw [if_neg h, if_neg h']

private lemma reflector_apply_eq_kmKernel_sum (P : Ω → X) (μ : Ω → ℚ) (ω : Ω) :
    reflector P μ ω = Finset.sum Finset.univ (fun ω' => kmKernel P ω ω' * μ ω') := by
  have hsum :
      Finset.sum Finset.univ (fun ω' => kmKernel P ω ω' * μ ω') =
        Finset.sum (fiberSet P (P ω)) (fun ω' => μ ω' * (fiberCard P (P ω) : ℚ)⁻¹) := by
    unfold fiberSet kmKernel
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro ω' _
    by_cases hEq : P ω' = P ω
    · rw [if_pos hEq, if_pos hEq.symm, div_eq_mul_inv]
      ring
    · have hEq' : P ω ≠ P ω' := fun h' => hEq h'.symm
      rw [if_neg hEq, if_neg hEq']
      simp
  unfold reflector uniformLift pushforward
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact hsum.symm

private lemma kmKernel_row_sum (P : Ω → X) (ω : Ω) :
    Finset.sum Finset.univ (fun ω' => kmKernel P ω ω') = 1 := by
  have hc : (fiberCard P (P ω) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fiberCard_pos_of_mem P ω)
  have hsum :
      Finset.sum Finset.univ (fun ω' => kmKernel P ω ω') =
        Finset.sum (fiberSet P (P ω)) (fun _ => (fiberCard P (P ω) : ℚ)⁻¹) := by
    unfold fiberSet kmKernel
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro ω' _
    by_cases hEq : P ω' = P ω
    · rw [if_pos hEq, if_pos hEq.symm, div_eq_mul_inv]
      simp
    · have hEq' : P ω ≠ P ω' := fun h' => hEq h'.symm
      rw [if_neg hEq, if_neg hEq']
  rw [hsum]
  simp [fiberCard, fiberSet, hc]

private lemma kmKernel_col_sum (P : Ω → X) (ω' : Ω) :
    Finset.sum Finset.univ (fun ω => kmKernel P ω ω') = 1 := by
  calc
    Finset.sum Finset.univ (fun ω => kmKernel P ω ω') =
        Finset.sum Finset.univ (fun ω => kmKernel P ω' ω) := by
      refine Finset.sum_congr rfl ?_
      intro ω _
      simpa using kmKernel_symm P ω ω'
    _ = 1 := kmKernel_row_sum P ω'

private lemma reflector_delta_eq_kmKernel (P : Ω → X) (ω ω' : Ω) :
    reflector P (deltaMass ω') ω = kmKernel P ω ω' := by
  rw [reflector_apply_eq_kmKernel_sum]
  unfold deltaMass
  rw [Finset.sum_eq_single ω']
  · simp [kmKernel]
  · intro η _ hη
    simp [hη]
  · simp

private lemma kmKernel_idempotent (P : Ω → X) (hP : Function.Surjective P) (ω ω' : Ω) :
    Finset.sum Finset.univ (fun η => kmKernel P ω η * kmKernel P η ω') = kmKernel P ω ω' := by
  have hIdem : reflectorIdempotent P := (paper_pom_fiber_reflector P hP).1
  have h :=
    congrFun (hIdem (deltaMass ω')) ω
  rw [reflector_apply_eq_kmKernel_sum, reflector_delta_eq_kmKernel] at h
  simpa [reflector_delta_eq_kmKernel] using h

/-- The reflector kernel is a symmetric idempotent bistochastic kernel whose action is fiberwise
averaging.
    prop:pom-Km-bistochastic -/
theorem paper_pom_km_bistochastic {Omega X : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype X] [DecidableEq X] (P : Omega → X) (hP : Function.Surjective P) : kmBistochastic P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω ω'
    exact kmKernel_symm P ω ω'
  · intro ω
    exact kmKernel_row_sum P ω
  · intro ω'
    exact kmKernel_col_sum P ω'
  · intro ω ω'
    exact kmKernel_idempotent P hP ω ω'
  · intro μ ω
    exact reflector_apply_eq_kmKernel_sum P μ ω

end FiberReflector

end Omega.POM.FiberReflector
