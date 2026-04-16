import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package recording the six front-end interface stages used in the typed-address
    biaxial completion chapter.
    prop:typed-address-biaxial-completion-front-interface -/
structure FrontInterfaceData where
  XFin : Type
  Xhat : Type
  PComp : Type
  AddrTyped : Type
  Readout : Type
  AuditLedger : Type
  SpecLayer : Type
  comp : XFin → Xhat
  phase : Xhat → PComp
  addr : PComp → AddrTyped
  Read_US : AddrTyped → Readout
  audit : Readout → AuditLedger
  spec : AuditLedger → SpecLayer

/-- Paper-facing wrapper: the recorded witness already determines the ordered front-end interface
    decomposition.
    prop:typed-address-biaxial-completion-front-interface -/
theorem paper_typed_address_biaxial_completion_front_interface
    (I : FrontInterfaceData) :
    ∃ comp : I.XFin → I.Xhat,
      ∃ phase : I.Xhat → I.PComp,
        ∃ addr : I.PComp → I.AddrTyped,
          ∃ Read_US : I.AddrTyped → I.Readout,
            ∃ audit : I.Readout → I.AuditLedger,
              ∃ spec : I.AuditLedger → I.SpecLayer,
                comp = I.comp ∧
                  phase = I.phase ∧
                  addr = I.addr ∧
                  Read_US = I.Read_US ∧ audit = I.audit ∧ spec = I.spec := by
  refine ⟨I.comp, I.phase, I.addr, I.Read_US, I.audit, I.spec, ?_⟩
  simp

end Omega.TypedAddressBiaxialCompletion
