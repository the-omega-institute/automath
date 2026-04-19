import Mathlib.Tactic
import Omega.Core.CoprimeSMul

namespace Omega

/-- In the torsion-free anomaly quotient, equality of normal forms plus equality of any one
nontrivial moment-anomaly slice already detects the original anomaly equality.
    thm:pom-anom-single-moment-complete-equivalence -/
theorem paper_pom_anom_single_moment_complete_equivalence {W N H : Type*} [AddCommGroup H]
    [NoZeroSMulDivisors ℤ H] (NF : W → N) (Anom : W → H) (MOM : ℤ → W → W) (q : ℤ) (hq : 2 ≤ q)
    (hAmp : ∀ w, Anom (MOM q w) = q • Anom w) (u v : W) :
    (NF u = NF v ∧ Anom u = Anom v) ↔
      (NF u = NF v ∧ Anom (MOM q u) = Anom (MOM q v)) := by
  constructor
  · rintro ⟨hNF, hAnom⟩
    refine ⟨hNF, ?_⟩
    rw [hAmp, hAmp, hAnom]
  · rintro ⟨hNF, hMom⟩
    refine ⟨hNF, ?_⟩
    have hq_ne : q ≠ 0 := by linarith
    let a : H := Anom u - Anom v
    have ha_zero : q • a = 0 := by
      dsimp [a]
      calc
        q • (Anom u - Anom v) = Anom (MOM q u) - Anom (MOM q v) := by
          rw [smul_sub, ← hAmp u, ← hAmp v]
        _ = 0 := sub_eq_zero.mpr hMom
    have ha : a = 0 := (torsion_free_smul_eq_zero_iff a q hq_ne).mp ha_zero
    exact sub_eq_zero.mp ha

end Omega
