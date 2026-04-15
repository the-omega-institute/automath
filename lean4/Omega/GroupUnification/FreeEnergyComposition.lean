import Mathlib

namespace Omega.GroupUnification

open scoped Topology

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the free-energy composition theorem in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:composition -/
theorem paper_zero_jitter_free_energy_composition
    (F Q R : ℝ → ℝ → ℝ) (phiInv logPhi : ℝ)
    (entropyComposition renyiCharacterization : Prop)
    (hComp : ∀ p s t, F (Q p t) s = F p (s + t - s * t) - (1 - s) * F p t)
    (hEntropy : entropyComposition)
    (hParry : ∀ p, Q p 1 = phiInv)
    (hAtOne : ∀ p, F p 1 = logPhi)
    (hRenyi : ∀ α p, α ≠ 1 → R α p = F p (1 - α) / (1 - α))
    (hCharacterize : renyiCharacterization) :
    (∀ p s t, F (Q p t) s = F p (s + t - s * t) - (1 - s) * F p t) ∧
      entropyComposition ∧
      (∀ α, α ≠ 1 → R α phiInv = logPhi) ∧
      renyiCharacterization := by
  refine ⟨hComp, hEntropy, ?_, hCharacterize⟩
  intro α hα
  have hF : F phiInv (1 - α) = (1 - α) * logPhi := by
    have hCompAtOne :
        F phiInv (1 - α) =
          F phiInv ((1 - α) + 1 - (1 - α) * 1) - (1 - (1 - α)) * F phiInv 1 := by
      simpa [hParry phiInv] using hComp phiInv (1 - α) 1
    calc
      F phiInv (1 - α) =
          F phiInv ((1 - α) + 1 - (1 - α) * 1) - (1 - (1 - α)) * F phiInv 1 :=
        hCompAtOne
      _ = F phiInv 1 - α * F phiInv 1 := by
        have hs : (1 - α) + 1 - (1 - α) * 1 = 1 := by ring
        have ht : 1 - (1 - α) = α := by ring
        rw [hs, ht]
      _ = logPhi - α * logPhi := by rw [hAtOne]
      _ = (1 - α) * logPhi := by ring
  have hne : 1 - α ≠ 0 := sub_ne_zero.mpr (by simpa using hα.symm)
  calc
    R α phiInv = F phiInv (1 - α) / (1 - α) := hRenyi α phiInv hα
    _ = ((1 - α) * logPhi) / (1 - α) := by rw [hF]
    _ = logPhi := by field_simp [hne]

end Omega.GroupUnification
