import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Omega.EA

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- The finite register family used in the bounded-feasibility statement. -/
abbrev DynamicPrimeRegister (k E : ℕ) := Fin k → Fin (E + 1)

private theorem exists_injective_into_fin_of_card_le (α : Type*) [Fintype α] {n : ℕ}
    (h : Fintype.card α ≤ n) : ∃ g : α → Fin n, Function.Injective g := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  refine ⟨fun a => Fin.castLE h (e a), ?_⟩
  intro a b hab
  apply e.injective
  apply Fin.ext
  simpa using congrArg Fin.val hab

private theorem exists_injective_of_card_le (α β : Type*) [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) : ∃ g : α → β, Function.Injective g := by
  classical
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  rcases exists_injective_into_fin_of_card_le α h with ⟨g, hg⟩
  exact ⟨fun a => e.symm (g a), e.symm.injective.comp hg⟩

/-- A lift into `X × register` exists exactly when every fiber of `f` fits into the register
capacity `(E + 1)^k`. Restricting an injective lift to a fiber gives the forward implication,
while the converse chooses injections fiberwise and assembles them into a global lift. -/
theorem paper_emergent_arithmetic_dynamic_prime_register_bounded_feasibility {Ω X : Type}
    [Fintype Ω] [Fintype X] (f : Ω → X) (hf : Function.Surjective f) (k E : ℕ) :
    (∃ ι : Ω → X × (Fin k → Fin (E + 1)), Function.Injective ι ∧ ∀ ω, (ι ω).1 = f ω) ↔
      Finset.univ.sup (fun x : X => Fintype.card {ω // f ω = x}) ≤ (E + 1) ^ k := by
  classical
  let R : Type := DynamicPrimeRegister k E
  have hcardR : Fintype.card R = (E + 1) ^ k := by
    simp [R, DynamicPrimeRegister]
  constructor
  · rintro ⟨ι, hι, hfst⟩
    refine Finset.sup_le ?_
    intro x hx
    let fiberLift : {ω // f ω = x} → R := fun ω => (ι ω.1).2
    have hFiberLift : Function.Injective fiberLift := by
      intro a b hab
      apply Subtype.ext
      apply hι
      apply Prod.ext
      · simpa [hfst] using a.2.trans b.2.symm
      · simpa [fiberLift] using hab
    have hcardFiber : Fintype.card {ω // f ω = x} ≤ Fintype.card R := by
      simpa [fiberLift] using Fintype.card_le_of_injective fiberLift hFiberLift
    simpa [hcardR] using hcardFiber
  · intro hBound
    have hFiberBound : ∀ x : X, Fintype.card {ω // f ω = x} ≤ Fintype.card R := by
      intro x
      exact le_trans
        (Finset.le_sup (s := Finset.univ) (f := fun y : X => Fintype.card {ω // f ω = y})
          (Finset.mem_univ x))
        (by simpa [hcardR] using hBound)
    choose g hg using
      fun x : X => exists_injective_of_card_le {ω // f ω = x} R (hFiberBound x)
    let toSigma : Ω → Sigma fun x : X => {ω // f ω = x} := fun ω => ⟨f ω, ⟨ω, rfl⟩⟩
    let sigmaLift : (Sigma fun x : X => {ω // f ω = x}) → X × R := fun s => (s.1, g s.1 s.2)
    have hToSigma : Function.Injective toSigma := by
      intro ω₁ ω₂ hEq
      exact congrArg (fun s => s.2.1) hEq
    have hSigmaLift : Function.Injective sigmaLift := by
      intro a b hEq
      cases a with
      | mk x u =>
          cases b with
          | mk y v =>
              dsimp [sigmaLift] at hEq ⊢
              have hxy : x = y := by
                simpa using congrArg Prod.fst hEq
              cases hxy
              have huv : g x u = g x v := by
                simpa using congrArg Prod.snd hEq
              have huvEq : u = v := hg x huv
              cases huvEq
              rfl
    refine ⟨fun ω => sigmaLift (toSigma ω), hSigmaLift.comp hToSigma, ?_⟩
    · intro ω
      rfl

end Omega.EA
