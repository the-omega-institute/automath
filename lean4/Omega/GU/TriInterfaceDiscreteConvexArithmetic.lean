import Omega.POM.MomentOddLagNeutrality
import Omega.Zeta.HankelRankMinimalLinearRealization
import Omega.Zeta.HankelStiffnessBalance
import Omega.Zeta.RealInput40RotationPolytopeShear

namespace Omega.GU

/-- Package theorem combining the audited discrete/convex/arithmetic interfaces already established
across the rotation-polytope shear, odd-lag neutrality, Hankel realization, and Hankel stiffness
files.
    thm:tri-interface-discrete-convex-arithmetic -/
theorem paper_tri_interface_discrete_convex_arithmetic {k : Type*} [Field k]
    (D : Omega.Zeta.RealInput40RotationPolytopeShearData)
    (H : Omega.Zeta.HankelMaximalMinorSyndromeData k) :
    (D.rot_chi = D.shear_image_rot_e ∧ D.support_function_pullback) ∧
      (Omega.POM.auditedMomentRecurrences.map Prod.fst = List.range' 2 22 ∧
        Omega.POM.auditedMomentRecurrences.map (fun entry => entry.snd.length % 2) =
          List.replicate 22 1 ∧
        Omega.POM.auditedMomentRecurrences.map (fun entry => Omega.POM.oddLagCoeffSum entry.snd) =
          List.replicate 22 (0 : ℤ) ∧
        Omega.POM.auditedMomentRecurrences.map
            (fun entry => Omega.POM.momentCharpolyParity entry.snd) =
          List.replicate 22 (0 : ℤ)) ∧
      (H.kernelLineGeneratedBySyndrome ∧ H.monicRecurrenceUnique ∧ H.shiftCompanionAnnihilated) ∧
      ((∀ a b t : ℤ, 2 * max (a + t) (b - t) ≥ a + b) ∧
        (∀ a b t : ℤ, max (a + t) (b - t) * 2 ≥ a + b) ∧
        (∀ a b : ℤ,
          max (a + Omega.Zeta.optimalT a b) (b - Omega.Zeta.optimalT a b) * 2 ≤ a + b + 1) ∧
        (∀ a b : ℤ,
          (a + b) % 2 = 0 →
            max (a + Omega.Zeta.optimalT a b) (b - Omega.Zeta.optimalT a b) * 2 = a + b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Omega.Zeta.paper_real_input_40_rotation_polytope_shear D
  · exact Omega.POM.paper_pom_moment_odd_lag_neutrality
  · exact Omega.Zeta.paper_xi_hankel_rank_minimal_linear_realization H
  · exact Omega.Zeta.paper_xi_hankel_stiffness_optimal_balance

end Omega.GU
