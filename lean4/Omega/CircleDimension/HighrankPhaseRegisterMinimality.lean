import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic
import Omega.CircleDimension.PhaseRegisterCommonAssignments
import Omega.CircleDimension.RegisterCircleModpFormula

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing high-rank package: the coordinatewise rank-one prime-fiber decomposition produces
the standard rank-`r` register profile, the register-circle mod-`p` formula reads off
`pcdim = r`, and every profinite cover of a full `Z_p^r` register has at least `r` generators.
    thm:cdim-highrank-phase-register-minimality -/
theorem paper_cdim_highrank_phase_register_minimality
    (r p : ℕ) [Fact p.Prime]
    {Lmod : Type} [AddCommGroup Lmod] [Module (ZMod p) Lmod] [FiniteDimensional (ZMod p) Lmod]
    (surj : Lmod →ₗ[ZMod p] (Fin r → ZMod p))
    (hsurj : Function.Surjective surj) :
    circleDim r 0 = r ∧
      ∃ K : RegisterCircleModpData,
        K.primes = ({p} : Finset Nat) ∧
          K.pcdim = r ∧
          K.zhatSurjectionDim = r ∧
          registerCirclePrimeSup K.primes K.modpDim = r ∧
          r ≤ Module.finrank (ZMod p) Lmod := by
  refine ⟨by simp [circleDim], ?_⟩
  let K : RegisterCircleModpData :=
    { primes := ({p} : Finset Nat)
      pcdim := r
      zhatSurjectionDim := r
      sylowPcdim := fun q => if q = p then r else 0
      modpDim := fun q => if q = p then r else 0
      sylowModpDim := fun q => if q = p then r else 0 }
  refine ⟨K, rfl, rfl, rfl, ?_, ?_⟩
  · have hFormula :=
      paper_cdim_register_circle_modp_formula K rfl
        (by simp [K, registerCirclePrimeSup, Finset.sup_singleton])
        (by
          intro q hq
          rfl)
        (by
          intro q hq
          rfl)
    rcases hFormula with ⟨_, hSup, _⟩
    simp [K, registerCirclePrimeSup, Finset.sup_singleton] at hSup ⊢
  · have hrange : LinearMap.range surj = ⊤ := LinearMap.range_eq_top.mpr hsurj
    calc
      r = Module.finrank (ZMod p) (Fin r → ZMod p) := by
        simp
      _ = Module.finrank (ZMod p) (LinearMap.range surj) := by
        rw [hrange, finrank_top]
      _ ≤ Module.finrank (ZMod p) Lmod := LinearMap.finrank_range_le surj

end Omega.CircleDimension
