import Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate
import Omega.RecursiveAddressing.NullAsLocalSectionObstruction

namespace Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion

open Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate

/-- Minimal acceptable-instantiation interface for the paper-facing physical-spacetime criterion.
It packages a local-global obstruction witness, a kernelized visible-sector interface, and a
continuum-limit witness. -/
structure AcceptableInstantiation where
  Addr : Type
  Obj : Type
  Visible : Type
  Fiber : Addr → Set Obj
  NullReadout : Addr → Prop
  Obstructed : Addr → Prop
  localGlobalTrivial : ∀ {a : Addr}, (Fiber a).Nonempty → ¬ Obstructed a
  localGlobalNull : ∀ {a : Addr}, Fiber a = (∅ : Set Obj) → NullReadout a
  witness : Addr
  witnessObstructed : Obstructed witness
  R : Setoid Visible
  K : Visible → Visible → ℝ
  hinv : ∀ {x x' y y'}, R.r x x' → R.r y y' → K x y = K x' y'
  hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → Visible) (a : ι → ℝ), 0 ≤ quadraticEnergy K ψ a
  continuumLimit : Prop
  continuumWitness : continuumLimit

/-- What it means for an acceptable instantiation to realize the paper's physical-spacetime
skeleton: the local-global obstruction is visible at the chosen witness, kernelization is
representative-independent and positive, and the continuum-limit ingredient is available. -/
def InstantiatesPhysicalSpacetime (I : AcceptableInstantiation) : Prop :=
  (I.Fiber I.witness = (∅ : Set I.Obj) ∧ I.NullReadout I.witness) ∧
    (∀ {ι : Type} [Fintype ι] (ψ ψ' : ι → I.Visible) (a : ι → ℝ),
      (∀ i, I.R.r (ψ i) (ψ' i)) →
        quadraticEnergy I.K ψ a = quadraticEnergy I.K ψ' a ∧
          0 ≤ quadraticEnergy I.K ψ a) ∧
    I.continuumLimit

/-- Paper-facing instantiation criterion: any acceptable instantiation already carries the three
ingredients needed by the chapter interface, namely a local-global obstruction witness, a
kernelized positive visible-sector package, and a continuum-limit witness.
    prop:physical-spacetime-instantiation-criterion -/
theorem paper_physical_spacetime_instantiation_criterion :
    ∀ I : AcceptableInstantiation, InstantiatesPhysicalSpacetime I := by
  intro I
  refine ⟨?_, ?_, I.continuumWitness⟩
  · exact
      Omega.RecursiveAddressing.paper_null_as_h2_obstruction
        I.Fiber I.NullReadout I.Obstructed I.localGlobalTrivial I.localGlobalNull
        I.witness I.witnessObstructed
  · intro ι _ ψ ψ' a hrep
    exact
      paper_physical_spacetime_kernelization_template_package
        I.R I.K I.hinv I.hpsd ψ ψ' a hrep

end Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion
