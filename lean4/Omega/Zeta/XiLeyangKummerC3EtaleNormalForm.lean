namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-kummer-c3-etale-normal-form`. -/
theorem paper_xi_leyang_kummer_c3_etale_normal_form
    (divisorTriple containsMu3 normOne cyclicEtaleCover pullbackTorsor : Prop)
    (hcover : divisorTriple → containsMu3 → cyclicEtaleCover)
    (htorsor : normOne → pullbackTorsor) :
    divisorTriple → containsMu3 → normOne → cyclicEtaleCover ∧ pullbackTorsor := by
  intro hdiv hmu hnorm
  exact ⟨hcover hdiv hmu, htorsor hnorm⟩

end Omega.Zeta
