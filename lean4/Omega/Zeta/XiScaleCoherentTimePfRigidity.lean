theorem paper_xi_scale_coherent_time_pf_rigidity
    (positiveConePrimitive uniqueProjectiveEigenray uniqueScaleGaugeRigid : Prop)
    (hpf : positiveConePrimitive -> uniqueProjectiveEigenray)
    (hscale : positiveConePrimitive -> uniqueScaleGaugeRigid) (h : positiveConePrimitive) :
    uniqueProjectiveEigenray ∧ uniqueScaleGaugeRigid := by
  exact ⟨hpf h, hscale h⟩
