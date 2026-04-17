import Mathlib.Tactic

namespace Omega.SPG

/-- Concrete package for the classification of a profinite torus extension by its Stokes module.
The Stokes module and integer lattice live inside a common ambient coordinate type, the split
criterion compares them, and the classification statement is represented by an equivalence between
the extension's isomorphism class and its Stokes-module descriptor. -/
structure ProfiniteTorusExtensionStokesModuleClassificationData where
  Coordinate : Type
  ExtensionIsoClass : Type
  StokesModuleClass : Type
  stokesModule : Set Coordinate
  integerLattice : Set Coordinate
  split : Prop
  integer_lattice_inclusion :
    integerLattice ⊆ stokesModule
  split_iff_integer_lattice :
    split ↔ stokesModule = integerLattice
  isoClassification :
    ExtensionIsoClass ≃ StokesModuleClass

/-- The ambient integer lattice sits inside the Stokes module. -/
def ProfiniteTorusExtensionStokesModuleClassificationData.integerLatticeIncluded
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) : Prop :=
  D.integerLattice ⊆ D.stokesModule

/-- The extension splits exactly when its Stokes module is the integer lattice. -/
def ProfiniteTorusExtensionStokesModuleClassificationData.splitIffIntegerLattice
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) : Prop :=
  D.split ↔ D.stokesModule = D.integerLattice

/-- The extension isomorphism class is completely determined by the Stokes-module class. -/
def ProfiniteTorusExtensionStokesModuleClassificationData.extensionIsoClassifiedByStokesModule
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) : Prop :=
  Nonempty (D.ExtensionIsoClass ≃ D.StokesModuleClass)

/-- Paper-facing wrapper for the Stokes-module classification of profinite torus extensions.
    prop:app-profinite-torus-extension-stokes-module-classification -/
theorem paper_app_profinite_torus_extension_stokes_module_classification
    (D : ProfiniteTorusExtensionStokesModuleClassificationData) :
    D.integerLatticeIncluded ∧ D.splitIffIntegerLattice ∧
      D.extensionIsoClassifiedByStokesModule := by
  refine ⟨D.integer_lattice_inclusion, ?_, ?_⟩
  · simpa [ProfiniteTorusExtensionStokesModuleClassificationData.splitIffIntegerLattice]
      using D.split_iff_integer_lattice
  · exact ⟨D.isoClassification⟩

end Omega.SPG
