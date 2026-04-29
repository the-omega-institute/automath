import Omega.Zeta.XiTimePart62debHologramAffineFullshiftConjugacy

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62deb-hologram-fullshift-entropy-primitive-zeta`. -/
theorem paper_xi_time_part62deb_hologram_fullshift_entropy_primitive_zeta
    (D : xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (topologicalEntropy periodicPointFormula primitiveOrbitFormula artinMazurZetaFormula : Prop)
    (hD : D.statement)
    (hEntropy : D.statement → topologicalEntropy)
    (hPeriodic : D.statement → periodicPointFormula)
    (hPrimitive : periodicPointFormula → primitiveOrbitFormula)
    (hZeta : periodicPointFormula → artinMazurZetaFormula) :
    topologicalEntropy ∧ periodicPointFormula ∧ primitiveOrbitFormula ∧
      artinMazurZetaFormula := by
  have hConjugacy : D.statement := hD
  have hPeriodicPointFormula : periodicPointFormula := hPeriodic hConjugacy
  exact
    ⟨hEntropy hConjugacy, hPeriodicPointFormula, hPrimitive hPeriodicPointFormula,
      hZeta hPeriodicPointFormula⟩

end Omega.Zeta
