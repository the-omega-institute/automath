import Omega.CircleDimension.S4V4KummerTorsorGeneratedByExplicit3torsion

namespace Omega.CircleDimension

/-- Paper label: `con:cdim-s4-a4-v4-jacobian-3torsor`. -/
theorem paper_cdim_s4_a4_v4_jacobian_3torsor (infinityFiber : Finset S4V4FiberPoint)
    (hcard : infinityFiber.card = 3) :
    let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
    divisorDegree D.pullbackInfinityDivisor = 3 ∧
      s4v4CompatibleBiellipticPencils.card = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor := by
  let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
  have htorsor := paper_cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion infinityFiber hcard
  change divisorDegree D.pullbackInfinityDivisor = 3 ∧
      s4v4CompatibleBiellipticPencils.card = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order = 3 ∧
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor
  exact ⟨htorsor.2.1, htorsor.2.2.1, htorsor.2.2.2.1, htorsor.2.2.2.2.1⟩

end Omega.CircleDimension
