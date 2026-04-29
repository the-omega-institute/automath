import Mathlib.Tactic
import Omega.SyncKernelWeighted.GmUniformTwistGapFromGcd

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted
open gm_uniform_twist_gap_from_gcd_data

/-- Analytic improvability means that every nontrivial modulus admits a uniform twist-gap package
compatible with the audited cycle gcd `d`. -/
def gm_improvability_iff_d1_analytically_improvable (d : ℕ) : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    ∃ D : gm_uniform_twist_gap_from_gcd_data,
      D.cycleGcd = d ∧ D.modulus = q ∧ D.has_uniform_twist_gap

/-- Canonical gap package when the audited cycle gcd is `1`: every modulus `q ≥ 2` fails to
divide the gcd, and the twisted radius `0` sits a fixed distance below the Perron radius `1`. -/
private def gm_improvability_iff_d1_canonical_gap_data (q : ℕ) (hq : 2 ≤ q) :
    gm_uniform_twist_gap_from_gcd_data where
  modulus := q
  cycleGcd := 1
  perronSpectralRadius := 1
  twistedSpectralRadius := 0
  modulus_not_dvd_cycleGcd := by
    intro hdiv
    have hq_eq : q = 1 := Nat.dvd_one.mp hdiv
    omega
  strictTwistedDrop := by norm_num

/-- Paper label: `thm:gm-improvability-iff-d1`. The finite-state model is analytically improvable
exactly when its cycle-gcd obstruction is trivial, namely `d = 1`. -/
theorem paper_gm_improvability_iff_d1 (d : ℕ) :
    gm_improvability_iff_d1_analytically_improvable d ↔ d = 1 := by
  constructor
  · intro himprov
    by_contra hd1
    by_cases hd0 : d = 0
    · rcases himprov 2 (by norm_num) with ⟨D, hcycle, hmod, hgap⟩
      rcases hgap with ⟨hnotdvd, _⟩
      have hdvd : D.modulus ∣ D.cycleGcd := by
        simpa [hcycle, hmod, hd0] using (show 2 ∣ 0 by norm_num)
      exact hnotdvd hdvd
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdge : 2 ≤ d := by omega
      rcases himprov d hdge with ⟨D, hcycle, hmod, hgap⟩
      rcases hgap with ⟨hnotdvd, _⟩
      have hdvd : D.modulus ∣ D.cycleGcd := by
        simpa [hcycle, hmod] using (dvd_rfl d)
      exact hnotdvd hdvd
  · intro hd1
    subst hd1
    intro q hq
    refine ⟨gm_improvability_iff_d1_canonical_gap_data q hq, rfl, rfl, ?_⟩
    exact paper_gm_uniform_twist_gap_from_gcd (gm_improvability_iff_d1_canonical_gap_data q hq)

end Omega.SyncKernelRealInput
