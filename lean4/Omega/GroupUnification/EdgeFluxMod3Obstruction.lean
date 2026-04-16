import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic

namespace Omega.GroupUnification.EdgeFluxMod3Obstruction

open Matrix

variable {n : ℕ}

/-- Reduce an integer matrix mod 3.
    cor:window6-edge-flux-mod3-obstruction -/
def reduceMod3 (E : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  E.map (fun x => (x : ZMod 3))

/-- If `3 ∣ det E`, then `det (reduceMod3 E) = 0`.
    cor:window6-edge-flux-mod3-obstruction -/
theorem reduceMod3_det_zero_of_three_dvd (E : Matrix (Fin n) (Fin n) ℤ)
    (h : (3 : ℤ) ∣ E.det) : (reduceMod3 E).det = 0 := by
  unfold reduceMod3
  have hcast_eq :
      (E.map (fun x : ℤ => (x : ZMod 3))) =
      (Int.castRingHom (ZMod 3)).mapMatrix E := rfl
  rw [hcast_eq]
  rw [← RingHom.map_det]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h

/-- Concrete `n = 1` instance: linear functional `χ(v) = v 0` is in the kernel.
    cor:window6-edge-flux-mod3-obstruction -/
theorem paper_window6_edge_flux_mod3_obstruction_n1
    (E : Matrix (Fin 1) (Fin 1) ℤ) (h : (3 : ℤ) ∣ E.det) :
    ∃ χ : (Fin 1 → ZMod 3) →ₗ[ZMod 3] ZMod 3,
      χ ≠ 0 ∧ ∀ v : Fin 1 → ℤ,
        χ (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) = 0 := by
  refine ⟨LinearMap.proj 0, ?_, ?_⟩
  · -- LinearMap.proj 0 ≠ 0 since (proj 0)(fun _ => 1) = 1
    intro hzero
    have : (LinearMap.proj 0 : (Fin 1 → ZMod 3) →ₗ[ZMod 3] ZMod 3) (fun _ => 1) = 0 := by
      rw [hzero]; rfl
    simp at this
  · intro v
    simp only [LinearMap.proj_apply]
    -- (E.mulVec v) 0 = E 0 0 * v 0 (det E = E 0 0 for 1x1)
    have hE : E.det = E 0 0 := Matrix.det_fin_one E
    have h3 : (3 : ℤ) ∣ E 0 0 := hE ▸ h
    have hmv : (E.mulVec v) 0 = E 0 0 * v 0 := by
      simp [Matrix.mulVec, dotProduct]
    rw [hmv]
    push_cast
    have : ((E 0 0 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3
    rw [this]
    ring

/-- Translation invariance of `χ` (general statement, conditional on existence).
    cor:window6-edge-flux-mod3-obstruction -/
theorem paper_window6_edge_flux_mod3_invariant
    (E : Matrix (Fin n) (Fin n) ℤ)
    (χ : (Fin n → ZMod 3) →ₗ[ZMod 3] ZMod 3)
    (hχ : ∀ v : Fin n → ℤ,
      χ (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) = 0)
    (b v : Fin n → ℤ) :
    χ (fun i => (((b + E.mulVec v) i : ℤ) : ZMod 3)) =
      χ (fun i => ((b i : ℤ) : ZMod 3)) := by
  have hsplit : (fun i => (((b + E.mulVec v) i : ℤ) : ZMod 3)) =
      (fun i => ((b i : ℤ) : ZMod 3)) +
        (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    rfl
  rw [hsplit, χ.map_add, hχ v, add_zero]

/-- General determinant-mod-3 obstruction: a singular reduction admits a nonzero
left-kernel functional annihilating every reduced image vector.
    cor:window6-edge-flux-mod3-obstruction -/
theorem paper_window6_edge_flux_mod3_obstruction {n : ℕ} (_hn : 0 < n)
    (E : Matrix (Fin n) (Fin n) ℤ) (h : (3 : ℤ) ∣ E.det) :
    ∃ χ : (Fin n → ZMod 3) →ₗ[ZMod 3] ZMod 3,
      χ ≠ 0 ∧ ∀ v : Fin n → ℤ, χ (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) = 0 := by
  let A : Matrix (Fin n) (Fin n) (ZMod 3) := reduceMod3 E
  have hdet : A.det = 0 := reduceMod3_det_zero_of_three_dvd E h
  obtain ⟨w, hwne, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  refine ⟨dotProductEquiv (ZMod 3) (Fin n) w, ?_, ?_⟩
  · intro hχ
    have hw0 : (dotProductEquiv (ZMod 3) (Fin n)) w = (dotProductEquiv (ZMod 3) (Fin n)) 0 := by
      simpa using hχ
    exact hwne ((dotProductEquiv (ZMod 3) (Fin n)).injective hw0)
  · intro v
    have hmul :
        (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) = A *ᵥ fun i => ((v i : ℤ) : ZMod 3) := by
      funext i
      simpa [A, reduceMod3, Function.comp_def] using
        (RingHom.map_mulVec (Int.castRingHom (ZMod 3)) E v i)
    change w ⬝ᵥ (fun i => ((E.mulVec v i : ℤ) : ZMod 3)) = 0
    rw [hmul, Matrix.dotProduct_mulVec, hw, zero_dotProduct]

end Omega.GroupUnification.EdgeFluxMod3Obstruction
