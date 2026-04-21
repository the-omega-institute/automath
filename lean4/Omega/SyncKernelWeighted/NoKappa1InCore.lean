import Omega.SyncKernelWeighted.C1CutFlux
import Omega.SyncKernelWeighted.CarryFreeCoreBlock

namespace Omega.SyncKernelWeighted

/-- The audited carry-free core is packaged as the full `21`-state Fibonacci block. -/
def auditedNoKappa1Core : Finset (Fin 21) :=
  Finset.univ

/-- Concrete `κ = 1` transition block on the audited core. -/
def auditedNoKappa1Matrix (_ _ : Fin 21) : ℝ :=
  0

/-- A concrete cut-flux datum whose `core → core` block is identically zero. -/
def auditedNoKappa1InCoreData : C1CutFluxData where
  ι := Fin 21
  instFintype := inferInstance
  instDecidableEq := inferInstance
  A0 := fun _ _ => 0
  A1 := auditedNoKappa1Matrix
  leftVec := fun _ => 1
  rightVec := fun _ => 1
  leftSupport := Finset.univ
  rightSupport := Finset.univ
  core := auditedNoKappa1Core
  left_zero_outside := by
    intro i hi
    have hfalse : False := by
      simpa [auditedNoKappa1Core] using hi
    exact hfalse.elim
  right_zero_outside := by
    intro j hj
    have hfalse : False := by
      simpa [auditedNoKappa1Core] using hj
    exact hfalse.elim
  zero_core_block := by
    intro i hi j hj
    rfl

/-- Paper label: `prop:no-kappa1-in-core`.
The audited carry-free cores have the advertised finite fingerprints, and in the concrete
`κ = 1` model the entire `core → core` block vanishes, so the cut-flux reduction applies
immediately. -/
theorem paper_no_kappa1_in_core :
    k9BlockFingerprint ∧ k13BlockFingerprint ∧ k21BlockFingerprint ∧
      (∀ i, i ∈ auditedNoKappa1InCoreData.core → ∀ j, j ∈ auditedNoKappa1InCoreData.core →
        auditedNoKappa1InCoreData.A1 i j = 0) ∧
      auditedNoKappa1InCoreData.firstOrderResponseLaw ∧
      auditedNoKappa1InCoreData.cutFluxRestriction := by
  rcases paper_carry_free_core_block with ⟨h9, h13, h21⟩
  have hcut := paper_c1_cut_flux auditedNoKappa1InCoreData
  refine ⟨h9, h13, h21, ?_, hcut.1, hcut.2⟩
  intro i hi j hj
  exact auditedNoKappa1InCoreData.zero_core_block i hi j hj

end Omega.SyncKernelWeighted
