namespace Omega.POM

/-- Paper-facing wrapper for the lcm-convolution and ghost linearization package.
    thm:pom-toggle-scan-cycle-ghost-multiplicativity -/
theorem paper_pom_toggle_scan_cycle_ghost_multiplicativity
    (lcmConvolution ghostProduct : Prop) (hConv : lcmConvolution)
    (hGhost : lcmConvolution -> ghostProduct) : And lcmConvolution ghostProduct := by
  exact ⟨hConv, hGhost hConv⟩

end Omega.POM
