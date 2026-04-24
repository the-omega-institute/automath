import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.MassSplittingMomentRoot

open scoped BigOperators

namespace Omega.POM

/-- The heavy-block `q`-th power sum. -/
def heavyPowerSum {Q : ℕ} (w : Fin Q → ℝ) (q : ℕ) : ℝ :=
  ∑ i, w i ^ q

/-- The heavy-block half-order quantity. -/
noncomputable def heavyHalfOrder {Q : ℕ} (w : Fin Q → ℝ) : ℝ :=
  ∑ i, Real.sqrt (w i)

/-- The unsplit baseline moment with a single light atom of mass `ε`. -/
def baselinePowerSum {Q : ℕ} (w : Fin Q → ℝ) (ε : ℝ) (q : ℕ) : ℝ :=
  heavyPowerSum w q + ε ^ q

/-- The split/camouflaged moment after replacing the light atom by the symbolic split
contribution `ε^q M^{1-q}`. -/
noncomputable def camouflagePowerSum {Q : ℕ} (w : Fin Q → ℝ) (ε : ℝ) (M q : ℕ) : ℝ :=
  heavyPowerSum w q + ε ^ q * (M : ℝ) ^ (1 - (q : ℝ))

/-- The unsplit half-order quantity. -/
noncomputable def baselineHalfOrder {Q : ℕ} (w : Fin Q → ℝ) (ε : ℝ) : ℝ :=
  heavyHalfOrder w + Real.sqrt ε

/-- The split half-order quantity with `M` equal light fragments of total mass `ε`. -/
noncomputable def camouflageHalfOrder {Q : ℕ} (w : Fin Q → ℝ) (ε : ℝ) (M : ℕ) : ℝ :=
  heavyHalfOrder w + (M : ℝ) * Real.sqrt (ε / M)

/-- A concrete finite-order camouflage package: if the heavy block absorbs the split-mass drift in
every moment `q = 1, ..., Q`, and if the heavy half-order drift is already controlled by an
`O(ε^2)` estimate, then the full split distribution matches all those moments exactly and its
half-order excess is the split contribution plus the same `O(ε^2)` heavy-block error.
    thm:pom-moment-camouflage-finite-orders -/
def POMMomentCamouflageFiniteOrdersStatement : Prop :=
  ∀ {Q M : ℕ} (a b : Fin Q → ℝ) {ε K : ℝ},
    2 ≤ Q →
    1 ≤ M →
    0 ≤ ε →
    heavyPowerSum b 1 = heavyPowerSum a 1 →
    (∀ q : ℕ, 2 ≤ q → q ≤ Q →
      heavyPowerSum b q = heavyPowerSum a q + ε ^ q * (1 - (M : ℝ) ^ (1 - (q : ℝ)))) →
    |heavyHalfOrder b - heavyHalfOrder a| ≤ K * ε ^ 2 →
    (∀ q : ℕ, 1 ≤ q → q ≤ Q → camouflagePowerSum b ε M q = baselinePowerSum a ε q) ∧
    |(camouflageHalfOrder b ε M - baselineHalfOrder a ε) -
        Real.sqrt ε * (Real.sqrt (M : ℝ) - 1)| ≤ K * ε ^ 2

theorem paper_pom_moment_camouflage_finite_orders :
    POMMomentCamouflageFiniteOrdersStatement := by
  intro Q M a b ε K hQ hM hε hmass hmom hsqrt
  refine ⟨?_, ?_⟩
  · intro q hq1 hqQ
    by_cases hq : q = 1
    · subst hq
      unfold camouflagePowerSum baselinePowerSum
      simp [hmass]
    · have hcorr := hmom q (by omega) hqQ
      unfold camouflagePowerSum baselinePowerSum
      linarith
  · have hsplit :
        (camouflageHalfOrder b ε M - baselineHalfOrder a ε) -
            Real.sqrt ε * (Real.sqrt (M : ℝ) - 1) =
          heavyHalfOrder b - heavyHalfOrder a := by
      unfold camouflageHalfOrder baselineHalfOrder
      have hs :=
        Omega.POM.MassSplittingMomentRoot.sqrt_diff ε M hε hM
      linarith
    simpa [hsplit] using hsqrt

end Omega.POM
