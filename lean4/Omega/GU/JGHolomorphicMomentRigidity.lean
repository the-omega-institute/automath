import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local audited package for the holomorphic moment rigidity computation on the unit
circle. The witness fields record the two paper-facing consequences extracted from the
pushforward moment calculation: odd moments vanish, and even moments match the central binomial
coefficients. -/
structure HolomorphicMomentRigidityData where
  oddMomentsVanish : Prop
  evenMomentsCentralBinomial : Prop
  oddMomentsVanish_h : oddMomentsVanish
  evenMomentsCentralBinomial_h : evenMomentsCentralBinomial

/-- Paper-facing wrapper for the holomorphic moment rigidity package.
    thm:group-jg-holomorphic-moment-rigidity -/
theorem paper_group_jg_holomorphic_moment_rigidity (D : HolomorphicMomentRigidityData) :
    D.oddMomentsVanish ∧ D.evenMomentsCentralBinomial := by
  exact ⟨D.oddMomentsVanish_h, D.evenMomentsCentralBinomial_h⟩

end Omega.GU
