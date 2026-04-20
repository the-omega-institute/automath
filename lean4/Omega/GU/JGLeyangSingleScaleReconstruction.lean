import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.GU

open Complex

/-- The unit-circle root predicate. -/
def leyangOnUnitCircle (z : ℂ) : Prop :=
  ‖z‖ = 1

/-- The transported `r⁻²`-circle root predicate. -/
def leyangOnInnerCircle (r : ℝ) (z : ℂ) : Prop :=
  ‖z‖ = (r⁻¹) ^ (2 : Nat)

/-- The radial transport sending unit-circle roots to the `r⁻²` circle. -/
noncomputable def leyangInnerScale (r : ℝ) (z : ℂ) : ℂ :=
  ((r⁻¹) ^ (2 : Nat) : ℝ) • z

/-- The inner transported root set. -/
noncomputable def leyangInnerTransport (r : ℝ) (S : Finset ℂ) : Finset ℂ :=
  S.image (leyangInnerScale r)

/-- The full transported root packet, containing the unit-circle factor and its inner partner. -/
noncomputable def leyangSingleScaleTransport (r : ℝ) (S : Finset ℂ) : Finset ℂ :=
  S ∪ leyangInnerTransport r S

/-- Recover the monic unit-circle factor by filtering for radius `1`. -/
noncomputable def leyangRecoverUnitFactor (S : Finset ℂ) : Finset ℂ :=
  S.filter fun z => ‖z‖ = 1

private theorem leyangInnerScale_norm
    {r : ℝ} (hr : 1 < r) {z : ℂ} (hz : leyangOnUnitCircle z) :
    ‖leyangInnerScale r z‖ = (r⁻¹) ^ (2 : Nat) := by
  have hnonneg : 0 ≤ (r⁻¹) ^ (2 : Nat) := by positivity
  calc
    ‖leyangInnerScale r z‖ = ‖((r⁻¹) ^ (2 : Nat) : ℝ)‖ * ‖z‖ := by
      rw [leyangInnerScale, norm_smul]
    _ = (r⁻¹) ^ (2 : Nat) * ‖z‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = (r⁻¹) ^ (2 : Nat) := by rw [hz, mul_one]

private theorem leyang_inv_sq_ne_one {r : ℝ} (hr : 1 < r) : (r⁻¹) ^ (2 : Nat) ≠ (1 : ℝ) := by
  have hr0 : r ≠ 0 := by linarith
  intro h
  have h' : r ^ (2 : Nat) * (r⁻¹) ^ (2 : Nat) = r ^ (2 : Nat) * 1 := by
    simpa using congrArg (fun x : ℝ => r ^ (2 : Nat) * x) h
  field_simp [hr0] at h'
  nlinarith [hr]

private theorem leyangRecoverUnitFactor_transport
    (r : ℝ) (S : Finset ℂ) (hr : 1 < r) (hS : ∀ z ∈ S, leyangOnUnitCircle z) :
    leyangRecoverUnitFactor (leyangSingleScaleTransport r S) = S := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzT, hzUnit⟩
    rcases Finset.mem_union.mp hzT with hzS | hzI
    · exact hzS
    · rcases Finset.mem_image.mp hzI with ⟨w, hwS, rfl⟩
      have hwUnit : leyangOnUnitCircle w := hS w hwS
      have hscaled : ‖leyangInnerScale r w‖ = (r⁻¹) ^ (2 : Nat) := leyangInnerScale_norm hr hwUnit
      have : ((r⁻¹) ^ (2 : Nat) : ℝ) = 1 := by rw [← hscaled, hzUnit]
      exact False.elim (leyang_inv_sq_ne_one hr this)
  · intro hzS
    exact Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inl hzS), hS z hzS⟩

/-- For `r > 1`, the unit-circle roots and the transported `r⁻²`-circle roots are disjoint, so
the unit-circle factor is recovered by filtering radius `1`, and the transport map is injective on
unit-circle root sets.
    cor:group-jg-leyang-single-scale-reconstruction -/
theorem paper_group_jg_leyang_single_scale_reconstruction
    (r : ℝ) (S₁ S₂ : Finset ℂ) (hr : 1 < r)
    (h₁ : ∀ z ∈ S₁, leyangOnUnitCircle z) (h₂ : ∀ z ∈ S₂, leyangOnUnitCircle z) :
    leyangRecoverUnitFactor (leyangSingleScaleTransport r S₁) = S₁ ∧
      leyangRecoverUnitFactor (leyangSingleScaleTransport r S₂) = S₂ ∧
      (leyangSingleScaleTransport r S₁ = leyangSingleScaleTransport r S₂ ↔ S₁ = S₂) := by
  have hrec₁ := leyangRecoverUnitFactor_transport r S₁ hr h₁
  have hrec₂ := leyangRecoverUnitFactor_transport r S₂ hr h₂
  refine ⟨hrec₁, hrec₂, ?_⟩
  constructor
  · intro hT
    have := congrArg leyangRecoverUnitFactor hT
    simpa [hrec₁, hrec₂] using this
  · intro hS
    simpa [hS]

end Omega.GU
