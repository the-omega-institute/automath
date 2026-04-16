import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Minimal group-valued transition data for local gluing. -/
structure TransitionData (ι G : Type*) [CommGroup G] where
  transition : ι → ι → G

/-- The residual of a loop is the product of its transition labels. -/
def loopResidual {ι G : Type*} [CommGroup G] (T : TransitionData ι G) (ℓ : List (ι × ι)) : G :=
  (ℓ.map fun e => T.transition e.1 e.2).prod

/-- A global section trivializes the transition data by expressing each transition as a gauge
    difference. -/
def admitsGlobalSection {ι G : Type*} [CommGroup G] (T : TransitionData ι G) : Prop :=
  ∃ s : ι → G, ∀ i j, T.transition i j = (s i)⁻¹ * s j

/-- Loop flatness means that every balanced loop has trivial residual. -/
def loopFlat {ι G : Type*} [CommGroup G] (T : TransitionData ι G) : Prop :=
  ∀ ℓ : List (ι × ι), (ℓ.map Prod.fst).Perm (ℓ.map Prod.snd) → loopResidual T ℓ = 1

/-- A nontrivial loop residual is the chapter-local witness for a gluing obstruction. -/
def obstructionWitness {ι G : Type*} [CommGroup G] (T : TransitionData ι G) : Prop :=
  ∃ ℓ : List (ι × ι), (ℓ.map Prod.fst).Perm (ℓ.map Prod.snd) ∧ loopResidual T ℓ ≠ 1

/-- Chapter-local packaging of the statement "the Čech obstruction class is nontrivial". -/
def cechObstructed {ι G : Type*} [CommGroup G] (T : TransitionData ι G) : Prop :=
  ¬ loopFlat T

private theorem section_product_telescope {ι G : Type*} [CommGroup G] (s : ι → G) :
    ∀ ℓ : List (ι × ι),
      (ℓ.map fun e => (s e.1)⁻¹ * s e.2).prod =
        ((ℓ.map fun e => s e.1).prod)⁻¹ * (ℓ.map fun e => s e.2).prod
  | [] => by simp
  | e :: ℓ => by
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
        List.prod_cons, section_product_telescope s ℓ]
      simp [mul_assoc, mul_left_comm, mul_comm]

private theorem globalSection_implies_loopFlat {ι G : Type*} [CommGroup G]
    (T : TransitionData ι G) (hGlobal : admitsGlobalSection T) : loopFlat T := by
  rcases hGlobal with ⟨s, hs⟩
  intro ℓ hPerm
  unfold loopResidual
  simp_rw [hs]
  rw [section_product_telescope]
  have hProd : (ℓ.map fun e => s e.1).prod = (ℓ.map fun e => s e.2).prod := by
    simpa using (hPerm.map s).prod_eq
  rw [hProd]
  simp

private theorem obstruction_of_not_loopFlat {ι G : Type*} [CommGroup G] (T : TransitionData ι G)
    (hObstructed : cechObstructed T) : obstructionWitness T := by
  by_contra hNoWitness
  apply hObstructed
  intro ℓ hPerm
  by_contra hResidual
  exact hNoWitness ⟨ℓ, hPerm, hResidual⟩

/-- Paper-facing wrapper for globalization versus loop flatness.
    In the minimal transition-data model, a global section telescopes every balanced loop product
    to the identity; conversely, any nontrivial gluing obstruction yields a loop with nontrivial
    residual.
    prop:typed-address-biaxial-completion-globalization-flatness -/
theorem paper_typed_address_biaxial_completion_globalization_flatness
    {ι G : Type*} [CommGroup G] (T : TransitionData ι G) :
    (admitsGlobalSection T → loopFlat T) ∧ (cechObstructed T → obstructionWitness T) := by
  refine ⟨globalSection_implies_loopFlat T, obstruction_of_not_loopFlat T⟩

end Omega.TypedAddressBiaxialCompletion
