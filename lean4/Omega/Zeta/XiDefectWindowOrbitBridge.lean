namespace Omega.Zeta

/-- Paper label: `thm:xi-defect-window-orbit-bridge`. -/
theorem paper_xi_defect_window_orbit_bridge
    (traceBridge finitePartInvariant kappaStable logMStable auditAbsorbed : Prop)
    (hTrace : traceBridge) (hFinite : traceBridge -> finitePartInvariant)
    (hAbsorb :
      traceBridge -> finitePartInvariant -> kappaStable -> logMStable -> auditAbsorbed)
    (hkappa : kappaStable) (hlogM : logMStable) :
    finitePartInvariant ∧ auditAbsorbed := by
  have hFinitePart : finitePartInvariant := hFinite hTrace
  exact ⟨hFinitePart, hAbsorb hTrace hFinitePart hkappa hlogM⟩

end Omega.Zeta
