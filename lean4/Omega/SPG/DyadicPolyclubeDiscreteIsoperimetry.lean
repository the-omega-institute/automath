import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.SPG.PolycubeIsoperimetryUpper

namespace Omega.SPG

open scoped BigOperators

/-- Chapter-local data for the dyadic polycube discrete isoperimetry package. The bulk cubes and
their exposed faces provide the linear upper bound via the existing union-count estimate. The
axial projection counts and directional face counts encode the fiber lower bound, together with
the discrete Loomis--Whitney and AM--GM inputs needed to package the natural-power lower bound. -/
structure DyadicPolyclubeDiscreteIsoperimetryData where
  n : ℕ
  N : ℕ
  F : ℕ
  bulk : Finset ℕ
  cubeFaces : ℕ → Finset ℕ
  exposedFaces : Finset ℕ
  projectionCount : Fin n → ℕ
  directionFaceCount : Fin n → ℕ
  bulk_card : bulk.card = N
  boundary_card : exposedFaces.card = F
  exposed_subset : exposedFaces ⊆ bulk.biUnion cubeFaces
  cube_faces_card_le : ∀ q ∈ bulk, (cubeFaces q).card ≤ 2 * n
  projection_faces_le : ∀ i, 2 * projectionCount i ≤ directionFaceCount i
  face_decomposition : (∑ i : Fin n, directionFaceCount i) = F
  loomis_whitney : N ^ (n - 1) ≤ ∏ i : Fin n, projectionCount i
  amgm_projection :
    (n ^ n) * ∏ i : Fin n, projectionCount i ≤ (∑ i : Fin n, projectionCount i) ^ n

/-- Dyadic polycube discrete isoperimetry in its paper-facing natural-power form.
    thm:spg-dyadic-polyclube-discrete-isoperimetry -/
theorem paper_spg_dyadic_polyclube_discrete_isoperimetry
    (h : Omega.SPG.DyadicPolyclubeDiscreteIsoperimetryData) :
    ((2 * h.n) ^ h.n) * h.N ^ (h.n - 1) ≤ h.F ^ h.n ∧ h.F ≤ 2 * h.n * h.N := by
  constructor
  · have hface_sum : 2 * ∑ i : Fin h.n, h.projectionCount i ≤ h.F := by
      calc
        2 * ∑ i : Fin h.n, h.projectionCount i = ∑ i : Fin h.n, 2 * h.projectionCount i := by
          rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin h.n, h.directionFaceCount i := by
          exact Finset.sum_le_sum fun i _hi => h.projection_faces_le i
        _ = h.F := h.face_decomposition
    calc
      ((2 * h.n) ^ h.n) * h.N ^ (h.n - 1) ≤
          ((2 * h.n) ^ h.n) * ∏ i : Fin h.n, h.projectionCount i := by
        exact Nat.mul_le_mul_left _ h.loomis_whitney
      _ = (2 ^ h.n) * ((h.n ^ h.n) * ∏ i : Fin h.n, h.projectionCount i) := by
        rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ (2 ^ h.n) * (∑ i : Fin h.n, h.projectionCount i) ^ h.n := by
        exact Nat.mul_le_mul_left _ h.amgm_projection
      _ = (2 * ∑ i : Fin h.n, h.projectionCount i) ^ h.n := by
        rw [← Nat.mul_pow]
      _ ≤ h.F ^ h.n := by
        exact Nat.pow_le_pow_left hface_sum _
  · have hupper :
        h.exposedFaces.card ≤ 2 * h.n * h.bulk.card :=
      Omega.SPG.PolycubeIsoperimetryUpper.paper_spg_dyadic_polyclube_discrete_isoperimetry_upper
        h.bulk h.cubeFaces h.n h.exposedFaces h.exposed_subset h.cube_faces_card_le
    simpa [h.boundary_card, h.bulk_card] using hupper

end Omega.SPG
