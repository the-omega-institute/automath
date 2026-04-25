import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-canonical-time-gauge-harmonic-representative`. -/
theorem paper_xi_canonical_time_gauge_harmonic_representative {V E : Type} [Fintype V]
    [Fintype E] [DecidableEq V] (src dst : E → V) (ℓ : E → ℝ) :
    ∃ b : V → ℝ, ∀ b' : V → ℝ,
      (∑ e, (ℓ e + b (dst e) - b (src e)) ^ 2 : ℝ) ≤
        ∑ e, (ℓ e + b' (dst e) - b' (src e)) ^ 2 := by
  classical
  let delta : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ E :=
    { toFun := fun b =>
        WithLp.toLp 2 (fun e => b (dst e) - b (src e))
      map_add' := by
        intro b₁ b₂
        ext e
        simp
        ring_nf
      map_smul' := by
        intro c b
        ext e
        simp
        ring_nf }
  let negℓ : EuclideanSpace ℝ E := WithLp.toLp 2 (fun e => -ℓ e)
  let U : Submodule ℝ (EuclideanSpace ℝ E) := LinearMap.range delta
  let p : EuclideanSpace ℝ E := U.starProjection negℓ
  have hp_mem : p ∈ U := by
    simp [p]
  rcases LinearMap.mem_range.mp hp_mem with ⟨bVec, hbVec⟩
  refine ⟨fun v => bVec v, ?_⟩
  intro b'
  let b'Vec : EuclideanSpace ℝ V := WithLp.toLp 2 b'
  have henergy :
      ∀ c : V → ℝ,
        (∑ e, (ℓ e + c (dst e) - c (src e)) ^ 2 : ℝ) =
          ‖negℓ - delta (WithLp.toLp 2 c)‖ ^ 2 := by
    intro c
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro e he
    simp [negℓ, delta, sub_eq_add_neg]
    ring
  have hnorm :
      ‖negℓ - delta bVec‖ ≤ ‖negℓ - delta b'Vec‖ := by
    have hproj :
        ‖negℓ - p‖ = ⨅ x : U, ‖negℓ - x‖ := by
      simpa [p] using (Submodule.starProjection_minimal (U := U) negℓ)
    have hle :
        ‖negℓ - p‖ ≤ ‖negℓ - ((⟨delta b'Vec, LinearMap.mem_range.mpr ⟨b'Vec, rfl⟩⟩ : U) : U)‖ := by
      rw [hproj]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _
    simpa [p, hbVec, b'Vec] using hle
  calc
    (∑ e, (ℓ e + bVec (dst e) - bVec (src e)) ^ 2 : ℝ)
        = ‖negℓ - delta bVec‖ ^ 2 := by
          simpa using henergy (fun v => bVec v)
    _ ≤ ‖negℓ - delta b'Vec‖ ^ 2 := by
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hnorm)
    _ = ∑ e, (ℓ e + b' (dst e) - b' (src e)) ^ 2 := by
      simpa [b'Vec] using (henergy b').symm

end Omega.Zeta
