import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SPG

noncomputable section

/-- The diagonal Gödel ellipsoid volume term `vol(B_r) * √N * R^r`. -/
def hypercubeCycleLatticeGodelEllipsoidVolume
    (rank godelInteger : ℕ) (unitBallVolume radius : ℝ) : ℝ :=
  unitBallVolume * Real.sqrt godelInteger * radius ^ rank

/-- The cycle-lattice main term obtained by dividing the ellipsoid volume by the covolume
`√τ(G)`. -/
def hypercubeCycleLatticeGodelCountMainTerm
    (rank godelInteger treeCount : ℕ) (unitBallVolume radius : ℝ) : ℝ :=
  hypercubeCycleLatticeGodelEllipsoidVolume rank godelInteger unitBallVolume radius /
    Real.sqrt treeCount

/-- The Gödel ellipsoid counting main term has the expected volume formula, covolume correction,
and logarithmic expansion. `cor:hypercube-cycle-lattice-godel-ellipsoid-counting` -/
theorem paper_hypercube_cycle_lattice_godel_ellipsoid_counting
    (rank godelInteger treeCount : ℕ) (unitBallVolume radius : ℝ)
    (hball : 0 < unitBallVolume) (hN : 0 < godelInteger) (htree : 0 < treeCount) (hR : 0 < radius) :
    hypercubeCycleLatticeGodelEllipsoidVolume rank godelInteger unitBallVolume radius =
      unitBallVolume * Real.sqrt godelInteger * radius ^ rank ∧
      hypercubeCycleLatticeGodelCountMainTerm rank godelInteger treeCount unitBallVolume radius =
        unitBallVolume * Real.sqrt godelInteger * radius ^ rank / Real.sqrt treeCount ∧
      Real.log (hypercubeCycleLatticeGodelCountMainTerm
          rank godelInteger treeCount unitBallVolume radius) =
        Real.log unitBallVolume + ((1 / 2 : ℝ) * Real.log godelInteger - (1 / 2 : ℝ) * Real.log treeCount) +
          (rank : ℝ) * Real.log radius := by
  have hsqrtN : 0 < Real.sqrt godelInteger := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtTree : 0 < Real.sqrt treeCount := by
    exact Real.sqrt_pos.2 (by exact_mod_cast htree)
  have hpow : 0 < radius ^ rank := by
    exact pow_pos hR _
  have hN_nonneg : (0 : ℝ) ≤ godelInteger := by
    exact_mod_cast Nat.zero_le godelInteger
  have htree_nonneg : (0 : ℝ) ≤ treeCount := by
    exact_mod_cast Nat.zero_le treeCount
  refine ⟨rfl, rfl, ?_⟩
  unfold hypercubeCycleLatticeGodelCountMainTerm hypercubeCycleLatticeGodelEllipsoidVolume
  have hmul :
      Real.log (unitBallVolume * Real.sqrt godelInteger * radius ^ rank) =
        Real.log unitBallVolume + Real.log (Real.sqrt godelInteger) + Real.log (radius ^ rank) := by
    rw [show unitBallVolume * Real.sqrt godelInteger * radius ^ rank =
        unitBallVolume * (Real.sqrt godelInteger * radius ^ rank) by ring]
    rw [Real.log_mul (ne_of_gt hball), Real.log_mul (ne_of_gt hsqrtN)]
    · ring
    · exact ne_of_gt hpow
    · exact mul_ne_zero (ne_of_gt hsqrtN) (ne_of_gt hpow)
  calc
    Real.log (unitBallVolume * Real.sqrt godelInteger * radius ^ rank / Real.sqrt treeCount)
        = Real.log (unitBallVolume * Real.sqrt godelInteger * radius ^ rank) -
            Real.log (Real.sqrt treeCount) := by
              rw [Real.log_div
                (mul_ne_zero (mul_ne_zero (ne_of_gt hball) (ne_of_gt hsqrtN)) (ne_of_gt hpow))
                (ne_of_gt hsqrtTree)]
    _ = Real.log unitBallVolume + Real.log (Real.sqrt godelInteger) + Real.log (radius ^ rank) -
          Real.log (Real.sqrt treeCount) := by rw [hmul]
    _ = Real.log unitBallVolume + ((1 / 2 : ℝ) * Real.log godelInteger) +
          (rank : ℝ) * Real.log radius - ((1 / 2 : ℝ) * Real.log treeCount) := by
            rw [Real.log_sqrt hN_nonneg, Real.log_sqrt htree_nonneg]
            rw [show radius ^ rank = radius ^ (rank : ℝ) by rw [Real.rpow_natCast]]
            rw [Real.log_rpow hR]
            ring
    _ = Real.log unitBallVolume +
          (((1 / 2 : ℝ) * Real.log godelInteger) - ((1 / 2 : ℝ) * Real.log treeCount)) +
            (rank : ℝ) * Real.log radius := by ring

end

end Omega.SPG
