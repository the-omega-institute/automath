namespace Omega.Zeta

universe u v

/-- Paper label: `cor:xi-null-z2-cech-obstruction-single-source-w1`. -/
theorem paper_xi_null_z2_cech_obstruction_single_source_w1 {H1 : Type u} {H2 : Type v}
    (tr : H1 → H2) (beta w1 zero1 : H1) (alpha2 zero2 : H2) (hw1 : w1 = beta)
    (htr : tr beta = alpha2) (hzero : beta = zero1 ↔ alpha2 = zero2) :
    alpha2 = tr w1 ∧ (alpha2 = zero2 ↔ w1 = zero1) := by
  constructor
  · rw [hw1]
    exact htr.symm
  · constructor
    · intro halpha
      rw [hw1]
      exact hzero.mpr halpha
    · intro hw1zero
      exact hzero.mp (hw1.symm.trans hw1zero)

end Omega.Zeta
