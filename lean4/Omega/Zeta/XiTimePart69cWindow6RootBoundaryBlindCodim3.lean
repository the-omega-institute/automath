import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The six-coordinate abelianized window model over `F2`. -/
abbrev xi_time_part69c_window6_root_boundary_blind_codim3_vector : Type :=
  Fin 6 → ZMod 2

/-- The projection that forgets the first three boundary coordinates and keeps the three
interior coordinates. -/
def xi_time_part69c_window6_root_boundary_blind_codim3_projection
    (x : xi_time_part69c_window6_root_boundary_blind_codim3_vector) : Fin 3 → ZMod 2 :=
  fun i => x ⟨i.val + 3, by omega⟩

/-- Boundary-coordinate inclusion: the first three coordinates are free and the projected
interior coordinates are zero. -/
def xi_time_part69c_window6_root_boundary_blind_codim3_boundaryEmbedding
    (b : Fin 3 → ZMod 2) : xi_time_part69c_window6_root_boundary_blind_codim3_vector :=
  fun j => if h : j.val < 3 then b ⟨j.val, h⟩ else 0

/-- Concrete finite-coordinate statement: the kernel of the projection is exactly the
three-coordinate boundary subspace, hence it has `2^3 = 8` elements. -/
def xi_time_part69c_window6_root_boundary_blind_codim3_statement : Prop :=
  (∀ x : xi_time_part69c_window6_root_boundary_blind_codim3_vector,
      xi_time_part69c_window6_root_boundary_blind_codim3_projection x = 0 ↔
        ∃ b : Fin 3 → ZMod 2,
          xi_time_part69c_window6_root_boundary_blind_codim3_boundaryEmbedding b = x) ∧
    Fintype.card (Fin 3 → ZMod 2) = 8

/-- Paper label: `thm:xi-time-part69c-window6-root-boundary-blind-codim3`. -/
theorem paper_xi_time_part69c_window6_root_boundary_blind_codim3 :
    xi_time_part69c_window6_root_boundary_blind_codim3_statement := by
  constructor
  · intro x
    constructor
    · intro hx
      refine ⟨fun i => x ⟨i.val, by omega⟩, ?_⟩
      funext j
      by_cases hj : j.val < 3
      · simp [xi_time_part69c_window6_root_boundary_blind_codim3_boundaryEmbedding, hj]
      · let i : Fin 3 := ⟨j.val - 3, by omega⟩
        have hidx : (⟨i.val + 3, by omega⟩ : Fin 6) = j := by
          ext
          simp [i]
          omega
        have hzero : x j = 0 := by
          have hcoord := congr_fun hx i
          have hcoord' : x (⟨i.val + 3, by omega⟩ : Fin 6) = 0 := by
            simpa [xi_time_part69c_window6_root_boundary_blind_codim3_projection] using hcoord
          simpa [hidx] using hcoord'
        simp [xi_time_part69c_window6_root_boundary_blind_codim3_boundaryEmbedding, hj, hzero]
    · rintro ⟨b, rfl⟩
      funext i
      have hnot : ¬ i.val + 3 < 3 := by omega
      simp [xi_time_part69c_window6_root_boundary_blind_codim3_projection,
        xi_time_part69c_window6_root_boundary_blind_codim3_boundaryEmbedding, hnot]
  · norm_num [Fintype.card_fun]

end Omega.Zeta
