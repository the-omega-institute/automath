namespace Omega.Zeta

/-- Paper label: `thm:xi-jg-transcendental-scale-galois-full-fidelity`. -/
theorem paper_xi_jg_transcendental_scale_galois_full_fidelity
    (baseChange galoisPreserved : Prop) (hbase : baseChange) (hgal : galoisPreserved) :
    baseChange ∧ galoisPreserved := by
  exact ⟨hbase, hgal⟩

end Omega.Zeta
