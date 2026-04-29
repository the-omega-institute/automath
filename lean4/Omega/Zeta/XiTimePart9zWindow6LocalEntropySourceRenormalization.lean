import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open BigOperators

namespace Omega.Zeta

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

theorem paper_xi_time_part9z_window6_local_entropy_source_renormalization {Λ Ω X : Type}
    [Fintype Λ] [Fintype Ω] [Fintype X] [DecidableEq X] (π : Ω → X)
    (W : Set (Λ → X)) [DecidablePred (fun w => w ∈ W)] (H : (Λ → X) → ℝ)
    (h : Ω → ℝ) (t : Λ → ℝ) :
    (∑ ω : {ω : Λ → Ω // (fun x => π (ω x)) ∈ W},
        Real.exp (-H (fun x => π (ω.1 x)) + ∑ x, t x * h (ω.1 x))) =
      ∑ w : {w : Λ → X // w ∈ W},
        Real.exp (-H w.1) *
          ∏ x : Λ, (∑ n : {n : Ω // π n = (w.1) x}, Real.exp (t x * h n.1)) := by
  classical
  let E₁ :
      {ω : Λ → Ω // (fun x => π (ω x)) ∈ W} ≃
        Σ w : {w : Λ → X // w ∈ W},
          {ω : Λ → Ω // (fun x => π (ω x)) = w.1} :=
    { toFun := fun ω =>
        ⟨⟨fun x => π (ω.1 x), ω.2⟩, ⟨ω.1, rfl⟩⟩
      invFun := fun s =>
        ⟨s.2.1, by
          rw [s.2.2]
          exact s.1.2⟩
      left_inv := by
        intro ω
        apply Subtype.ext
        rfl
      right_inv := by
        intro s
        rcases s with ⟨⟨w, hw⟩, ω, hω⟩
        dsimp at hω
        cases hω
        rfl }
  let fiberEquiv :
      (w : {w : Λ → X // w ∈ W}) →
        {ω : Λ → Ω // (fun x => π (ω x)) = w.1} ≃
          ((x : Λ) → {n : Ω // π n = (w.1) x}) :=
    fun w =>
      (Equiv.subtypeEquivRight (α := Λ → Ω) (p := fun ω => (fun x => π (ω x)) = w.1)
          (q := fun ω => ∀ x, π (ω x) = (w.1) x) (fun ω => by
            constructor
            · intro hω x
              exact congrFun hω x
            · intro hω
              funext x
              exact hω x)).trans
        (Equiv.subtypePiEquivPi (β := fun _ : Λ => Ω)
          (p := fun x n => π n = (w.1) x))
  let E :
      {ω : Λ → Ω // (fun x => π (ω x)) ∈ W} ≃
        Σ w : {w : Λ → X // w ∈ W}, (x : Λ) → {n : Ω // π n = (w.1) x} :=
    E₁.trans (Equiv.sigmaCongrRight fiberEquiv)
  let F :
      (Σ w : {w : Λ → X // w ∈ W}, (x : Λ) → {n : Ω // π n = (w.1) x}) → ℝ :=
    fun s => Real.exp (-H s.1.1 + ∑ x, t x * h ((s.2 x).1))
  calc
    (∑ ω : {ω : Λ → Ω // (fun x => π (ω x)) ∈ W},
        Real.exp (-H (fun x => π (ω.1 x)) + ∑ x, t x * h (ω.1 x))) =
        ∑ s : (Σ w : {w : Λ → X // w ∈ W},
          (x : Λ) → {n : Ω // π n = (w.1) x}), F s := by
      refine Fintype.sum_equiv E _ _ ?_
      intro ω
      simp [E, E₁, fiberEquiv, F, Equiv.subtypeEquivRight, Equiv.subtypeEquiv,
        Equiv.subtypePiEquivPi]
    _ =
        ∑ w : {w : Λ → X // w ∈ W},
          ∑ f : (x : Λ) → {n : Ω // π n = (w.1) x}, F ⟨w, f⟩ := by
      rw [Fintype.sum_sigma]
    _ =
        ∑ w : {w : Λ → X // w ∈ W},
          Real.exp (-H w.1) *
            ∑ f : (x : Λ) → {n : Ω // π n = (w.1) x},
              ∏ x : Λ, Real.exp (t x * h ((f x).1)) := by
      simp [F, Real.exp_add, Real.exp_sum, Finset.mul_sum]
    _ =
        ∑ w : {w : Λ → X // w ∈ W},
          Real.exp (-H w.1) *
            ∏ x : Λ, (∑ n : {n : Ω // π n = (w.1) x}, Real.exp (t x * h n.1)) := by
      congr with w
      rw [Fintype.prod_sum]

end

end Omega.Zeta
