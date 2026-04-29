import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Omega.POM

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- The fiber cardinality of `f` above `x`. -/
noncomputable def pom_injectivization_sideinfo_exact_alphabet_fiberCard
    {Omega X : Type*} [Fintype Omega] [Fintype X] (f : Omega → X) (x : X) : ℕ :=
  Fintype.card {ω // f ω = x}

/-- The exact side-information alphabet size is the largest fiber of `f`. -/
noncomputable def pom_injectivization_sideinfo_exact_alphabet_budget
    {Omega X : Type*} [Fintype Omega] [Fintype X] (f : Omega → X) : ℕ :=
  Finset.univ.sup (fun x : X => pom_injectivization_sideinfo_exact_alphabet_fiberCard f x)

/-- The paper-facing exact-alphabet package: every injective refinement of `f` into `X × [R]`
forces `R` to dominate the maximal fiber size, and the maximal fiber size is itself realizable by
an injective refinement. -/
def pom_injectivization_sideinfo_exact_alphabet_statement
    {Omega X : Type*} [Fintype Omega] [Fintype X] (f : Omega → X) : Prop :=
  let D := pom_injectivization_sideinfo_exact_alphabet_budget f
  (∀ R : ℕ, (∃ s : Omega → Fin R, Function.Injective (fun ω => (f ω, s ω))) → D ≤ R) ∧
    ∃ s : Omega → Fin D, Function.Injective (fun ω => (f ω, s ω))

private theorem pom_injectivization_sideinfo_exact_alphabet_exists_injective_into_fin_of_card_le
    (α : Type*) [Fintype α] {n : ℕ} (h : Fintype.card α ≤ n) :
    ∃ g : α → Fin n, Function.Injective g := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  refine ⟨fun a => Fin.castLE h (e a), ?_⟩
  intro a b hab
  apply e.injective
  apply Fin.ext
  simpa using congrArg Fin.val hab

/-- Paper label: `prop:pom-injectivization-sideinfo-exact-alphabet`. Injectivity on each fiber
forces pairwise distinct side-information labels, so the exact alphabet size is the maximal fiber
cardinality; conversely, one can choose a fiberwise code into `Fin D_f` and assemble it into a
global injective refinement. -/
theorem paper_pom_injectivization_sideinfo_exact_alphabet {Omega X : Type*} [Fintype Omega]
    [Fintype X] (f : Omega → X) : pom_injectivization_sideinfo_exact_alphabet_statement f := by
  classical
  dsimp [pom_injectivization_sideinfo_exact_alphabet_statement]
  let D := pom_injectivization_sideinfo_exact_alphabet_budget f
  refine ⟨?_, ?_⟩
  · intro R hRefine
    rcases hRefine with ⟨s, hs⟩
    have hfiberBound :
        ∀ x : X, pom_injectivization_sideinfo_exact_alphabet_fiberCard f x ≤ R := by
      intro x
      let code : {ω // f ω = x} → Fin R := fun ω => s ω.1
      have hcode : Function.Injective code := by
        intro a b hab
        apply Subtype.ext
        apply hs
        apply Prod.ext
        · simpa using a.2.trans b.2.symm
        · simpa [code] using hab
      simpa [pom_injectivization_sideinfo_exact_alphabet_fiberCard, code] using
        Fintype.card_le_of_injective code hcode
    refine Finset.sup_le ?_
    intro x hx
    exact hfiberBound x
  · have hfiberBound :
        ∀ x : X, pom_injectivization_sideinfo_exact_alphabet_fiberCard f x ≤ D := by
      intro x
      exact le_trans
        (Finset.le_sup
          (s := Finset.univ)
          (f := fun y : X => pom_injectivization_sideinfo_exact_alphabet_fiberCard f y)
          (Finset.mem_univ x))
        le_rfl
    choose code hcode using
      fun x : X =>
        pom_injectivization_sideinfo_exact_alphabet_exists_injective_into_fin_of_card_le
          {ω // f ω = x} (hfiberBound x)
    let toSigma : Omega → Sigma fun x : X => {ω // f ω = x} := fun ω => ⟨f ω, ⟨ω, rfl⟩⟩
    let sigmaLift : (Sigma fun x : X => {ω // f ω = x}) → X × Fin D :=
      fun s => (s.1, code s.1 s.2)
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
              have huv : code x u = code x v := by
                simpa using congrArg Prod.snd hEq
              have huvEq : u = v := hcode x huv
              cases huvEq
              rfl
    refine ⟨fun ω => (sigmaLift (toSigma ω)).2, ?_⟩
    intro ω₁ ω₂ hEq
    have hpair : sigmaLift (toSigma ω₁) = sigmaLift (toSigma ω₂) := by
      simpa [sigmaLift, toSigma] using hEq
    exact hToSigma (hSigmaLift hpair)

end Omega.POM
