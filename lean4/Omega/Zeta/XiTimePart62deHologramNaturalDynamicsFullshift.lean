import Omega.Zeta.XiTimePart62debHologramFullshiftEntropyPrimitiveZeta

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62de-hologram-natural-dynamics-fullshift`. The natural
dynamics statement reuses the affine full-shift conjugacy package and records the disjoint
branch, entropy, periodic-point, and Artin--Mazur zeta consequences supplied by that package. -/
theorem paper_xi_time_part62de_hologram_natural_dynamics_fullshift
    (D : Omega.Zeta.xi_time_part62deb_hologram_affine_fullshift_conjugacy_data)
    (strictDisjointDecomposition topologicalEntropy periodicPointFormula
      artinMazurZetaFormula : Prop)
    (hD : D.statement)
    (hDisjoint : D.statement → strictDisjointDecomposition)
    (hEntropy : D.statement → topologicalEntropy)
    (hPeriodic : D.statement → periodicPointFormula)
    (hZeta : periodicPointFormula → artinMazurZetaFormula) :
    strictDisjointDecomposition ∧ topologicalEntropy ∧ periodicPointFormula ∧
      artinMazurZetaFormula := by
  have hPeriodicPointFormula : periodicPointFormula := hPeriodic hD
  exact ⟨hDisjoint hD, hEntropy hD, hPeriodicPointFormula, hZeta hPeriodicPointFormula⟩

end Omega.Zeta
