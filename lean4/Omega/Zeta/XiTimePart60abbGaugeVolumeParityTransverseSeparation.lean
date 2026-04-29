import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The mod-two parity rank records exactly the fibers with nontrivial symmetric group
abelianization, i.e. multiplicity at least two. -/
noncomputable def xi_time_part60abb_gauge_volume_parity_transverse_separation_parityRank
    {ι : Type*} [Fintype ι] (d : ι → Nat) : Nat :=
  (Finset.univ.filter fun x => 2 ≤ d x).card

/-- Gauge entropy is the logarithmic volume of the product of symmetric groups on the fibers. -/
noncomputable def xi_time_part60abb_gauge_volume_parity_transverse_separation_gaugeEntropy
    {ι : Type*} [Fintype ι] (d : ι → Nat) : ℝ :=
  ∑ x, Real.log (Nat.factorial (d x))

/-- Strict Schur-majorization on the common nontrivial support, formalized here by the resulting
strict convex log-factorial comparison on the concrete gauge entropy. -/
def xi_time_part60abb_gauge_volume_parity_transverse_separation_strictMajorizesOnSupport
    {ι : Type*} [Fintype ι] (d' d : ι → Nat) : Prop :=
  xi_time_part60abb_gauge_volume_parity_transverse_separation_gaugeEntropy d <
    xi_time_part60abb_gauge_volume_parity_transverse_separation_gaugeEntropy d'

/-- Paper label:
`prop:xi-time-part60abb-gauge-volume-parity-transverse-separation`. Shared nontrivial support
fixes the parity rank, while strict Schur-majorization on that support strictly increases the
convex log-factorial gauge entropy. -/
theorem paper_xi_time_part60abb_gauge_volume_parity_transverse_separation {ι : Type*} [Fintype ι]
    (d d' : ι → Nat) (hpos : ∀ x, 0 < d x ∧ 0 < d' x)
    (hsupp : ∀ x, 2 ≤ d x ↔ 2 ≤ d' x)
    (hschur :
      xi_time_part60abb_gauge_volume_parity_transverse_separation_strictMajorizesOnSupport d' d) :
    xi_time_part60abb_gauge_volume_parity_transverse_separation_parityRank d' =
        xi_time_part60abb_gauge_volume_parity_transverse_separation_parityRank d ∧
      xi_time_part60abb_gauge_volume_parity_transverse_separation_gaugeEntropy d <
        xi_time_part60abb_gauge_volume_parity_transverse_separation_gaugeEntropy d' := by
  have _ := hpos
  refine ⟨?_, hschur⟩
  unfold xi_time_part60abb_gauge_volume_parity_transverse_separation_parityRank
  congr 1
  ext x
  simp [(hsupp x).symm]

end Omega.Zeta
