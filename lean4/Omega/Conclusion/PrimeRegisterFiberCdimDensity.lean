import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Omega.CircleDimension.CircleDim

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- The normalized prime-register fiber counting ratio, indexed by `n + 1` so the denominator is
    never zero. Here `s n` should be read as the finite subfiber size `|S_n|`. -/
noncomputable def primeFiberDensitySeq (s : ℕ → ℕ) (n : ℕ) : ℝ :=
  (s (n + 1) : ℝ) / (n + 1 : ℝ)

/-- The corresponding normalized half-circle-dimension ratio. -/
noncomputable def primeFiberCdimSeq (s : ℕ → ℕ) (n : ℕ) : ℝ :=
  (((Omega.CircleDimension.halfCircleDim (s (n + 1)) 0 : ℚ) : ℝ) /
    ((Omega.CircleDimension.halfCircleDim (n + 1) 0 : ℚ) : ℝ))

/-- Upper normalized half-circle dimension for a prime subfiber sequence. -/
noncomputable def primeFiberUpperCdim (s : ℕ → ℕ) : ℝ :=
  limsup (primeFiberCdimSeq s) atTop

/-- Lower normalized half-circle dimension for a prime subfiber sequence. -/
noncomputable def primeFiberLowerCdim (s : ℕ → ℕ) : ℝ :=
  liminf (primeFiberCdimSeq s) atTop

/-- Upper natural density of the prime index set. -/
noncomputable def primeFiberUpperDensity (s : ℕ → ℕ) : ℝ :=
  limsup (primeFiberDensitySeq s) atTop

/-- Lower natural density of the prime index set. -/
noncomputable def primeFiberLowerDensity (s : ℕ → ℕ) : ℝ :=
  liminf (primeFiberDensitySeq s) atTop

lemma primeFiberCdimSeq_eq_densitySeq (s : ℕ → ℕ) (n : ℕ) :
    primeFiberCdimSeq s n = primeFiberDensitySeq s n := by
  unfold primeFiberCdimSeq primeFiberDensitySeq
  rw [show (((Omega.CircleDimension.halfCircleDim (s (n + 1)) 0 : ℚ) : ℝ)) =
      (s (n + 1) : ℝ) / 2 by
    simp [Omega.CircleDimension.halfCircleDim, Omega.CircleDimension.circleDim]]
  rw [show (((Omega.CircleDimension.halfCircleDim (n + 1) 0 : ℚ) : ℝ)) =
      (n + 1 : ℝ) / 2 by
    simp [Omega.CircleDimension.halfCircleDim, Omega.CircleDimension.circleDim]]
  have hne : ((n + 1 : ℝ) / 2) ≠ 0 := by positivity
  field_simp [hne]

lemma primeFiberAbsSub_eq_div (s s' : ℕ → ℕ) (n : ℕ) :
    |primeFiberCdimSeq s n - primeFiberCdimSeq s' n| =
      |(s (n + 1) : ℝ) - s' (n + 1)| / (n + 1 : ℝ) := by
  rw [primeFiberCdimSeq_eq_densitySeq, primeFiberCdimSeq_eq_densitySeq]
  unfold primeFiberDensitySeq
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  have hsub :
      (s (n + 1) : ℝ) / (n + 1 : ℝ) - (s' (n + 1) : ℝ) / (n + 1 : ℝ) =
        ((s (n + 1) : ℝ) - s' (n + 1)) / (n + 1 : ℝ) := by
    field_simp [hne]
  rw [hsub, abs_div]
  have hpos : 0 ≤ (n + 1 : ℝ) := by positivity
  simp [abs_of_nonneg hpos]

set_option maxHeartbeats 400000 in
/-- Paper-facing density law for prime-register fibers: the normalized half-circle-dimension
    sequence agrees pointwise with the prime-index density sequence, hence has the same limsup,
    liminf, and limit when the latter exists; bounded finite-symmetric-difference perturbations
    decay on the `O(1 / n)` scale.
    thm:conclusion-prime-register-fiber-cdim-density -/
theorem paper_conclusion_prime_register_fiber_cdim_density
    (s s' : ℕ → ℕ) (ρ C : ℝ)
    (hbound : ∀ n, |(s (n + 1) : ℝ) - s' (n + 1)| ≤ C)
    (hρ : Tendsto (primeFiberDensitySeq s) atTop (𝓝 ρ)) :
    primeFiberUpperCdim s = primeFiberUpperDensity s ∧
      primeFiberLowerCdim s = primeFiberLowerDensity s ∧
      Tendsto (primeFiberCdimSeq s) atTop (𝓝 ρ) ∧
      Tendsto (fun n => |primeFiberCdimSeq s n - primeFiberCdimSeq s' n|) atTop (𝓝 0) := by
  have hseq : primeFiberCdimSeq s = primeFiberDensitySeq s :=
    funext (primeFiberCdimSeq_eq_densitySeq s)
  have hupper : primeFiberUpperCdim s = primeFiberUpperDensity s := by
    simp [primeFiberUpperCdim, primeFiberUpperDensity, hseq]
  have hlower : primeFiberLowerCdim s = primeFiberLowerDensity s := by
    simp [primeFiberLowerCdim, primeFiberLowerDensity, hseq]
  have htendsto : Tendsto (primeFiberCdimSeq s) atTop (𝓝 ρ) := by
    simpa [hseq] using hρ
  have hden0 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using hden0
  have habs :
      Tendsto (fun n : ℕ => |(s (n + 1) : ℝ) - s' (n + 1)| / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ |(s (n + 1) : ℝ) - s' (n + 1)| :=
      Filter.Eventually.of_forall fun _ => abs_nonneg _
    have hle : ∀ᶠ n : ℕ in atTop, |(s (n + 1) : ℝ) - s' (n + 1)| ≤ C :=
      Filter.Eventually.of_forall hbound
    exact tendsto_bdd_div_atTop_nhds_zero hnonneg hle hden
  have hfinite :
      Tendsto (fun n => |primeFiberCdimSeq s n - primeFiberCdimSeq s' n|) atTop (𝓝 0) := by
    simpa [primeFiberAbsSub_eq_div] using habs
  exact ⟨hupper, hlower, htendsto, hfinite⟩

end Omega.Conclusion
