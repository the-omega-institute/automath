import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9vk-no-finite-local-analytic-transform-from-resonance-germ-to-foldpi-tail`. -/
theorem paper_xi_time_part9vk_no_finite_local_analytic_transform_from_resonance_germ_to_foldpi_tail
    (positiveRadius zeroRadius finiteLocalTransformExists : Prop)
    (hpreserve : finiteLocalTransformExists -> positiveRadius)
    (htail : finiteLocalTransformExists -> zeroRadius)
    (hcontra : positiveRadius -> zeroRadius -> False) :
    Not finiteLocalTransformExists := by
  intro hfinite
  exact hcontra (hpreserve hfinite) (htail hfinite)

end Omega.Zeta
