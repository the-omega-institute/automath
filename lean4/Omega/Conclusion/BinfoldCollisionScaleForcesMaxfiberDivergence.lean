import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Divergence to `+∞` measured against natural thresholds. -/
def NatDivergesToInfinity (f : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, ∃ m : ℕ, (K : ℝ) ≤ f m

/-- The normalized collision scale `N_m * Col_m`. -/
def binfoldCollisionScaleTerm (N Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  N m * Col m

/-- The scaled `L²` excess obtained from the collision identity. -/
def binfoldScaledL2Term (N Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  binfoldCollisionScaleTerm N Col m - 1

/-- The maxfiber-to-average ratio. -/
noncomputable def binfoldMaxfiberRatioTerm (M avg : ℕ → ℝ) (m : ℕ) : ℝ :=
  M m / avg m

/-- The scaled `L²` excess diverges. -/
def scaledL2Diverges (N Col : ℕ → ℝ) : Prop :=
  NatDivergesToInfinity (binfoldScaledL2Term N Col)

/-- The maxfiber-to-average ratio diverges. -/
def maxfiberRatioDiverges (M avg : ℕ → ℝ) : Prop :=
  NatDivergesToInfinity (binfoldMaxfiberRatioTerm M avg)

private theorem scaledL2Diverges_of_collisionScaleDiverges
    (N Col : ℕ → ℝ)
    (hCollisionDiv : NatDivergesToInfinity (binfoldCollisionScaleTerm N Col)) :
    scaledL2Diverges N Col := by
  intro K
  obtain ⟨m, hm⟩ := hCollisionDiv (K + 1)
  refine ⟨m, ?_⟩
  have hm' : (K : ℝ) + 1 ≤ binfoldCollisionScaleTerm N Col m := by
    simpa [binfoldCollisionScaleTerm, Nat.cast_add] using hm
  dsimp [binfoldScaledL2Term]
  linarith

private theorem le_one_add_sqrt_of_sq_le {K : ℕ} {x : ℝ}
    (hK : (K : ℝ) ^ 2 ≤ x) :
    (K : ℝ) ≤ 1 + Real.sqrt x := by
  have hsqrt : Real.sqrt ((K : ℝ) ^ 2) ≤ Real.sqrt x := by
    exact Real.sqrt_le_sqrt hK
  have hk : (K : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_sq_eq_abs] at hsqrt
    simpa using hsqrt
  linarith

/-- Rewriting the collision identity as `N_m * Col_m - 1` gives the scaled `L²` excess; if the
finite-layer maxfiber ratio dominates `1 + √(N_m * Col_m - 1)`, then divergence of the
collision scale forces divergence of the maxfiber-to-average ratio.
    thm:conclusion-binfold-collision-scale-forces-maxfiber-divergence -/
theorem paper_conclusion_binfold_collision_scale_forces_maxfiber_divergence
    (N Col M avg : ℕ → ℝ)
    (hCollisionLower : ∀ m, 1 ≤ binfoldCollisionScaleTerm N Col m)
    (hCollisionDiv : NatDivergesToInfinity (binfoldCollisionScaleTerm N Col))
    (hMaxfiberLower :
      ∀ m, 1 + Real.sqrt (binfoldScaledL2Term N Col m) ≤ binfoldMaxfiberRatioTerm M avg m) :
    scaledL2Diverges N Col ∧ maxfiberRatioDiverges M avg := by
  have hScaledDiv : scaledL2Diverges N Col :=
    scaledL2Diverges_of_collisionScaleDiverges N Col hCollisionDiv
  refine ⟨hScaledDiv, ?_⟩
  intro K
  obtain ⟨m, hm⟩ := hScaledDiv (K * K)
  refine ⟨m, ?_⟩
  have hx : 0 ≤ binfoldScaledL2Term N Col m := by
    have hLower : 1 ≤ N m * Col m := by
      simpa [binfoldCollisionScaleTerm] using hCollisionLower m
    dsimp [binfoldScaledL2Term, binfoldCollisionScaleTerm]
    linarith
  have hsquare : (K : ℝ) ^ 2 ≤ binfoldScaledL2Term N Col m := by
    simpa [pow_two, Nat.cast_mul] using hm
  have hk : (K : ℝ) ≤ 1 + Real.sqrt (binfoldScaledL2Term N Col m) :=
    le_one_add_sqrt_of_sq_le hsquare
  exact le_trans hk (hMaxfiberLower m)

end Omega.Conclusion
