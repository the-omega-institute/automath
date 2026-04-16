import Mathlib.Data.Finset.Order
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Finite-prime supremum of a mod-`p` generator-count profile. -/
def registerCirclePrimeSup (primes : Finset Nat) (f : Nat → Nat) : Nat :=
  primes.sup f

/-- Seed data for a profinite register together with its Sylow and mod-`p` generator profiles. -/
structure RegisterCircleModpData where
  primes : Finset Nat
  pcdim : Nat
  zhatSurjectionDim : Nat
  sylowPcdim : Nat → Nat
  modpDim : Nat → Nat
  sylowModpDim : Nat → Nat

private theorem registerCirclePrimeSup_eq_of_pointwise_eq
    (primes : Finset Nat) (f g : Nat → Nat) (hfg : ∀ p ∈ primes, f p = g p) :
    registerCirclePrimeSup primes f = registerCirclePrimeSup primes g := by
  unfold registerCirclePrimeSup
  refine le_antisymm ?_ ?_
  · exact Finset.sup_le fun p hp => by
      simpa [hfg p hp] using (Finset.le_sup hp : g p ≤ primes.sup g)
  · exact Finset.sup_le fun p hp => by
      simpa [hfg p hp] using (Finset.le_sup hp : f p ≤ primes.sup f)

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the profinite register circle-dimension formula:
    the `Ẑ^d`-surjection generator count agrees with the supremum of the Sylow generator counts,
    and the same supremum can be read mod `p`.
    thm:cdim-register-circle-modp-formula -/
theorem paper_cdim_register_circle_modp_formula
    (K : RegisterCircleModpData)
    (hSurjection : K.pcdim = K.zhatSurjectionDim)
    (hSylowSup : K.pcdim = registerCirclePrimeSup K.primes K.sylowPcdim)
    (hSylowModp : ∀ p ∈ K.primes, K.modpDim p = K.sylowModpDim p)
    (hGenerator : ∀ p ∈ K.primes, K.sylowPcdim p = K.sylowModpDim p) :
    K.pcdim = K.zhatSurjectionDim ∧
      K.pcdim = registerCirclePrimeSup K.primes K.modpDim ∧
      (∀ p ∈ K.primes, K.modpDim p = K.sylowModpDim p) := by
  have hPointwise : ∀ p ∈ K.primes, K.sylowPcdim p = K.modpDim p := by
    intro p hp
    calc
      K.sylowPcdim p = K.sylowModpDim p := hGenerator p hp
      _ = K.modpDim p := (hSylowModp p hp).symm
  have hSup :
      registerCirclePrimeSup K.primes K.sylowPcdim =
        registerCirclePrimeSup K.primes K.modpDim :=
    registerCirclePrimeSup_eq_of_pointwise_eq K.primes K.sylowPcdim K.modpDim hPointwise
  exact ⟨hSurjection, hSylowSup.trans hSup, hSylowModp⟩

end Omega.CircleDimension
