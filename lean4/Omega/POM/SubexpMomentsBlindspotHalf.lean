import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.POM.MomentCamouflageFiniteOrders

namespace Omega.POM

open Real

/-- The exponentially small light mass used in the blindspot construction. -/
noncomputable def blindspotLightMass (β : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-β * (m : ℝ))

lemma blindspotLightMass_nonneg (β : ℝ) (m : ℕ) :
    0 ≤ blindspotLightMass β m := by
  unfold blindspotLightMass
  positivity

lemma sqrt_exp_half (x : ℝ) :
    Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have hrew : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrew]
  simpa using Real.sqrt_mul_self (Real.exp_nonneg (x / 2))

lemma sqrt_blindspotLightMass (β : ℝ) (m : ℕ) :
    Real.sqrt (blindspotLightMass β m) = Real.exp (-(β * (m : ℝ)) / 2) := by
  unfold blindspotLightMass
  simpa using sqrt_exp_half (-β * (m : ℝ))

lemma split_half_boost_lower_bound {α β : ℝ} {m M : ℕ}
    (hMexp : Real.exp (α * (m : ℝ)) ≤ M) :
    Real.sqrt (blindspotLightMass β m) * (Real.sqrt (M : ℝ) - 1) ≥
      Real.exp (((α - β) * (m : ℝ)) / 2) - Real.exp (-(β * (m : ℝ)) / 2) := by
  have hsqrtM :
      Real.exp ((α * (m : ℝ)) / 2) ≤ Real.sqrt (M : ℝ) := by
    rw [← sqrt_exp_half (α * (m : ℝ))]
    exact Real.sqrt_le_sqrt hMexp
  have hfactor :
      Real.exp ((α * (m : ℝ)) / 2) - 1 ≤ Real.sqrt (M : ℝ) - 1 := by
    linarith
  have hmass : 0 ≤ Real.exp (-(β * (m : ℝ)) / 2) := by positivity
  have hmul :
      Real.exp (-(β * (m : ℝ)) / 2) * (Real.exp ((α * (m : ℝ)) / 2) - 1) ≤
        Real.sqrt (blindspotLightMass β m) * (Real.sqrt (M : ℝ) - 1) := by
    rw [sqrt_blindspotLightMass]
    exact mul_le_mul_of_nonneg_left hfactor hmass
  have hrew :
      Real.exp (-(β * (m : ℝ)) / 2) * (Real.exp ((α * (m : ℝ)) / 2) - 1) =
        Real.exp (((α - β) * (m : ℝ)) / 2) - Real.exp (-(β * (m : ℝ)) / 2) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    Real.exp (((α - β) * (m : ℝ)) / 2) - Real.exp (-(β * (m : ℝ)) / 2)
        = Real.exp (-(β * (m : ℝ)) / 2) * (Real.exp ((α * (m : ℝ)) / 2) - 1) := by
            rw [hrew]
    _ ≤ Real.sqrt (blindspotLightMass β m) * (Real.sqrt (M : ℝ) - 1) := hmul

/-- Specializing the finite-order camouflage package to the exponential light mass
`ε_m = exp(-β m)` and to a split multiplicity `M` at least `exp(α m)` gives exact moment
matching up to the subexponential cutoff `Q`, and the half-order observable still enjoys the
explicit exponential-scale lower bound coming from the split mass.
    thm:pom-subexp-moments-blindspot-half -/
theorem paper_pom_subexp_moments_blindspot_half
    {Q M m : ℕ} (a b : Fin Q → ℝ) {α β K : ℝ}
    (hQ : 2 ≤ Q)
    (hM : 1 ≤ M)
    (hsubexp : (Q : ℝ) ≤ Real.exp (α * (m : ℝ)))
    (hMexp : Real.exp (α * (m : ℝ)) ≤ M)
    (hmass : heavyPowerSum b 1 = heavyPowerSum a 1)
    (hmom : ∀ q : ℕ, 2 ≤ q → q ≤ Q →
      heavyPowerSum b q =
        heavyPowerSum a q + blindspotLightMass β m ^ q * (1 - (M : ℝ) ^ (1 - (q : ℝ))))
    (hsqrt : |heavyHalfOrder b - heavyHalfOrder a| ≤ K * blindspotLightMass β m ^ 2) :
    Q ≤ M ∧
      (∀ q : ℕ, 1 ≤ q → q ≤ Q →
        camouflagePowerSum b (blindspotLightMass β m) M q =
          baselinePowerSum a (blindspotLightMass β m) q) ∧
      camouflageHalfOrder b (blindspotLightMass β m) M -
          baselineHalfOrder a (blindspotLightMass β m) ≥
        Real.exp (((α - β) * (m : ℝ)) / 2) - Real.exp (-(β * (m : ℝ)) / 2) -
          K * blindspotLightMass β m ^ 2 := by
  have hQleM_real : (Q : ℝ) ≤ M := le_trans hsubexp hMexp
  have hQleM : Q ≤ M := by exact_mod_cast hQleM_real
  have hcam :=
    paper_pom_moment_camouflage_finite_orders (Q := Q) (M := M) a b
      (ε := blindspotLightMass β m) (K := K) hQ hM
      (blindspotLightMass_nonneg β m) hmass hmom hsqrt
  rcases hcam with ⟨hmatch, herr⟩
  have hboost :=
    split_half_boost_lower_bound (α := α) (β := β) (m := m) (M := M) hMexp
  have hlower :
      camouflageHalfOrder b (blindspotLightMass β m) M -
          baselineHalfOrder a (blindspotLightMass β m) ≥
        Real.sqrt (blindspotLightMass β m) * (Real.sqrt (M : ℝ) - 1) -
          K * blindspotLightMass β m ^ 2 := by
    have hleft := (abs_le.mp herr).1
    linarith
  refine ⟨hQleM, hmatch, ?_⟩
  linarith

end Omega.POM
