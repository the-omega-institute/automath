import Omega.GroupUnification.FreeEnergyComposition
import Omega.GroupUnification.TiltDynamics

namespace Omega.GroupUnification

open scoped Topology

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the tilted free-energy theorem in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:tilted-free-energy -/
theorem paper_zero_jitter_tilted_free_energy
    (T F rho : ℝ → ℝ → ℝ) (L : ℝ → ℝ) (phiInv logPhi : ℝ)
    (analyticity derivativeFormula relativeEntropyIdentity : Prop)
    (hLog : ∀ p t, F p t = Real.log (rho p t))
    (hCoord : ∀ t p, L (T t p) = (1 - t) * L p)
    (hZero : ∀ p, L p = 0 ↔ p = phiInv)
    (hInj : Function.Injective L)
    (hComp : ∀ p s t, F (T t p) s = F p (s + t - s * t) - (1 - s) * F p t)
    (hUnit : ∀ p, T 1 p = phiInv)
    (hAtOne : ∀ p, F p 1 = logPhi)
    (hAnalyticity : analyticity)
    (hDerivative : derivativeFormula)
    (hRelativeEntropy : relativeEntropyIdentity) :
    (∀ p t, F p t = Real.log (rho p t)) ∧
      (∀ t n p, L ((T t)^[n] p) = (1 - t) ^ n * L p) ∧
      (∀ t, T t phiInv = phiInv) ∧
      (∀ t n p, (T t)^[n] p = T (1 - (1 - t) ^ n) p) ∧
      (∀ p s t, F (T t p) s = F p (s + t - s * t) - (1 - s) * F p t) ∧
      (∀ p, T 1 p = phiInv) ∧
      (∀ α p, α ≠ 1 → F (T 1 p) (1 - α) / (1 - α) = logPhi) ∧
      analyticity ∧
      derivativeFormula ∧
      relativeEntropyIdentity := by
  obtain ⟨hIter, hFixed, hSemigroup, _, _⟩ :=
    paper_zero_jitter_tilt_dynamics T L phiInv hCoord hZero hInj
  have hRenyiAtUnit : ∀ α p, α ≠ 1 → F (T 1 p) (1 - α) / (1 - α) = logPhi := by
    intro α p hα
    have hne : 1 - α ≠ 0 := sub_ne_zero.mpr (by simpa using hα.symm)
    have hBase :
        F (T 1 p) (1 - α) = (1 - α) * logPhi := by
      calc
        F (T 1 p) (1 - α) = F p ((1 - α) + 1 - (1 - α) * 1) - (1 - (1 - α)) * F p 1 :=
          hComp p (1 - α) 1
        _ = F p 1 - α * F p 1 := by ring
        _ = logPhi - α * logPhi := by rw [hAtOne]
        _ = (1 - α) * logPhi := by ring
    calc
      F (T 1 p) (1 - α) / (1 - α) = ((1 - α) * logPhi) / (1 - α) := by rw [hBase]
      _ = logPhi := by field_simp [hne]
  exact
    ⟨hLog, hIter, hFixed, hSemigroup, hComp, hUnit, hRenyiAtUnit, hAnalyticity, hDerivative,
      hRelativeEntropy⟩

end Omega.GroupUnification
