import Omega.Zeta.XiTimePart9odEscortEscortFdivBinaryClosure

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9ob-escort-lastbit-bernoulli-fdiv`. -/
theorem paper_xi_time_part9ob_escort_lastbit_bernoulli_fdiv (f : ℝ → ℝ) (p q : ℕ) :
    xiEscortBinaryFDivLimit f p q =
      (1 - xiEscortTheta p) * f ((1 - xiEscortTheta q) / (1 - xiEscortTheta p)) +
        xiEscortTheta p * f (xiEscortTheta q / xiEscortTheta p) := by
  rw [paper_xi_time_part9od_escort_escort_fdiv_binary_closure]

end Omega.Zeta
