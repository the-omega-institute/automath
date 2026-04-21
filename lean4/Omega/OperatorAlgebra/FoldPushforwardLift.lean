import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Concrete finite fold data for pushforward, the fiber-uniform lift, and the associated
fiber-averaging operator. -/
structure FoldPushforwardLiftData where
  Ω : Type
  X : Type
  instDecEqΩ : DecidableEq Ω
  instFintypeΩ : Fintype Ω
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  fold : Ω → X
  fold_surjective : Function.Surjective fold

attribute [instance] FoldPushforwardLiftData.instDecEqΩ
attribute [instance] FoldPushforwardLiftData.instFintypeΩ
attribute [instance] FoldPushforwardLiftData.instDecEqX
attribute [instance] FoldPushforwardLiftData.instFintypeX

namespace FoldPushforwardLiftData

/-- The finite fiber over a visible state. -/
def fiber (D : FoldPushforwardLiftData) (x : D.X) : Finset D.Ω :=
  Finset.univ.filter fun a => D.fold a = x

/-- Fiber cardinality. -/
def fiberCard (D : FoldPushforwardLiftData) (x : D.X) : ℕ :=
  (D.fiber x).card

/-- Pushforward of a finite weight function along the fold map. -/
def pushforward (D : FoldPushforwardLiftData) (μ : D.Ω → ℚ) (x : D.X) : ℚ :=
  Finset.sum (D.fiber x) μ

/-- Fiber-uniform lift from visible weights back to the source space. -/
def lift (D : FoldPushforwardLiftData) (π : D.X → ℚ) (a : D.Ω) : ℚ :=
  π (D.fold a) / D.fiberCard (D.fold a)

/-- Fiberwise average of an observable, indexed by the visible state. -/
def fiberAverageX (D : FoldPushforwardLiftData) (f : D.Ω → ℚ) (x : D.X) : ℚ :=
  D.pushforward f x / D.fiberCard x

/-- The conditional expectation onto the fiber-constant observables. -/
def expectation (D : FoldPushforwardLiftData) (f : D.Ω → ℚ) (a : D.Ω) : ℚ :=
  D.fiberAverageX f (D.fold a)

/-- Finite expectation pairing between observables and weights on `Ω`. -/
def pairing (D : FoldPushforwardLiftData) (f μ : D.Ω → ℚ) : ℚ :=
  Finset.sum Finset.univ fun a => f a * μ a

/-- Coordinate form of the pushforward formula. -/
def pushforwardFormula (D : FoldPushforwardLiftData) : Prop :=
  ∀ μ x, D.pushforward μ x = Finset.sum (D.fiber x) μ

/-- The fiber-uniform lift is a section of pushforward. -/
def pushforwardLiftId (D : FoldPushforwardLiftData) : Prop :=
  ∀ π x, D.pushforward (D.lift π) x = π x

/-- The fiber-averaging operator is adjoint to the Markov kernel `Q_m ∘ P_m`. -/
def adjointness (D : FoldPushforwardLiftData) : Prop :=
  ∀ f μ, D.pairing (D.expectation f) μ = D.pairing f (D.lift (D.pushforward μ))

lemma mem_fiber_self (D : FoldPushforwardLiftData) (a : D.Ω) : a ∈ D.fiber (D.fold a) := by
  simp [fiber]

lemma fiber_nonempty (D : FoldPushforwardLiftData) (x : D.X) : (D.fiber x).Nonempty := by
  rcases D.fold_surjective x with ⟨a, rfl⟩
  exact ⟨a, D.mem_fiber_self a⟩

lemma fiberCard_pos (D : FoldPushforwardLiftData) (x : D.X) : 0 < D.fiberCard x := by
  simpa [fiberCard] using (D.fiber_nonempty x).card_pos

lemma pushforward_lift_apply (D : FoldPushforwardLiftData) (π : D.X → ℚ) (x : D.X) :
    D.pushforward (D.lift π) x = π x := by
  have hcardq : (D.fiberCard x : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos x)
  calc
    D.pushforward (D.lift π) x
        = Finset.sum (D.fiber x) (fun a => π (D.fold a) / D.fiberCard (D.fold a)) := by
            rfl
    _ = Finset.sum (D.fiber x) (fun a => π x / D.fiberCard x) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hax : D.fold a = x := by
            simpa [fiber] using ha
          simp [hax]
    _ = (D.fiberCard x : ℚ) * (π x / D.fiberCard x) := by
          simp [fiberCard]
    _ = π x := by
          field_simp [hcardq]

lemma expectation_eq_on_fiberAverageX (D : FoldPushforwardLiftData) (f : D.Ω → ℚ) (x : D.X)
    (a : D.Ω) (ha : a ∈ D.fiber x) :
    D.expectation f a = D.fiberAverageX f x := by
  have hax : D.fold a = x := by
    simpa [fiber] using ha
  simp [expectation, fiberAverageX, hax]

lemma adjointness_apply (D : FoldPushforwardLiftData) (f μ : D.Ω → ℚ) :
    D.pairing (D.expectation f) μ = D.pairing f (D.lift (D.pushforward μ)) := by
  calc
    D.pairing (D.expectation f) μ
        = Finset.sum Finset.univ
            (fun x => Finset.sum (D.fiber x) fun a => D.expectation f a * μ a) := by
            unfold pairing
            symm
            simpa [fiber] using
              (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
                (g := D.fold) (h := fun _ _ => by simp)
                (f := fun a => D.expectation f a * μ a))
    _ = Finset.sum Finset.univ (fun x => D.fiberAverageX f x * D.pushforward μ x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          calc
            Finset.sum (D.fiber x) (fun a => D.expectation f a * μ a)
                = Finset.sum (D.fiber x) (fun a => D.fiberAverageX f x * μ a) := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    rw [D.expectation_eq_on_fiberAverageX f x a ha]
            _ = D.fiberAverageX f x * D.pushforward μ x := by
                  simp [pushforward, Finset.mul_sum]
    _ = Finset.sum Finset.univ
          (fun x => D.pushforward f x * (D.pushforward μ x / D.fiberCard x)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [fiberAverageX, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = Finset.sum Finset.univ
          (fun x => Finset.sum (D.fiber x) fun a => f a * (D.pushforward μ x / D.fiberCard x)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [pushforward, Finset.sum_mul]
    _ = Finset.sum Finset.univ
          (fun x => Finset.sum (D.fiber x) fun a => f a * D.lift (D.pushforward μ) a) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hax : D.fold a = x := by
            simpa [fiber] using ha
          simp [lift, hax]
    _ = D.pairing f (D.lift (D.pushforward μ)) := by
          unfold pairing
          simpa [fiber] using
            (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
              (g := D.fold) (h := fun _ _ => by simp)
              (f := fun a => f a * D.lift (D.pushforward μ) a))

end FoldPushforwardLiftData

open FoldPushforwardLiftData

/-- The fold pushforward is given fiberwise by summation, the fiber-uniform lift is a right
inverse, and the fiber-average operator is adjoint to the induced Markov kernel.
    prop:fold-pushforward-lift -/
theorem paper_fold_pushforward_lift (D : FoldPushforwardLiftData) :
    D.pushforwardFormula ∧ D.pushforwardLiftId ∧ D.adjointness := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun μ x => rfl
  · intro π x
    exact D.pushforward_lift_apply π x
  · intro f μ
    exact D.adjointness_apply f μ

end Omega.OperatorAlgebra
