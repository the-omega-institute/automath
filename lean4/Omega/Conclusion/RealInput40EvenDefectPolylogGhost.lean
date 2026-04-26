import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.RealInput40RootUnityGhostCompletePrimitiveDegenerate

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Specialized primitive defect for the real-input-`40` Euler factor `(1 - u z²)`. -/
def conclusion_realinput40_even_defect_polylog_ghost_primitive_defect
    (n : ℕ) (u : ℂ) : ℂ :=
  atomPrimitiveCoeff n u

/-- Specialized ghost defect for the same single Euler factor. -/
def conclusion_realinput40_even_defect_polylog_ghost_ghost_defect (n : ℕ) (u : ℂ) : ℂ :=
  atomGhostCoeff n u

/-- Primitive cumulative step obtained by summing the specialized primitive defect. -/
def conclusion_realinput40_even_defect_polylog_ghost_primitive_step
    (N : ℕ) (u : ℂ) : ℂ :=
  Finset.sum (Finset.range (N + 1))
    (fun n => conclusion_realinput40_even_defect_polylog_ghost_primitive_defect n u)

/-- Chapter-local formal polylog ghost for the even defect. -/
def conclusion_realinput40_even_defect_polylog_ghost_polylog (s : ℕ) (u : ℂ) : ℂ :=
  ((2 : ℂ) ^ s) * u

/-- The even-length ghost Dirichlet series is the explicit polylog factor `2^(1-s) Li_s(u)`. -/
def conclusion_realinput40_even_defect_polylog_ghost_dirichlet_series (s : ℕ) (u : ℂ) : ℂ :=
  ((2 : ℂ) / (2 : ℂ) ^ s) *
    conclusion_realinput40_even_defect_polylog_ghost_polylog s u

/-- Paper label: `cor:conclusion-realinput40-even-defect-polylog-ghost`. Specializing the
single-Euler-factor surgery to `(m, ell, E) = (1, 2, 1)` gives the length-`2` primitive defect and
the even-only ghost tail; summing the primitive defect yields an exact Heaviside step, and the
Dirichlet ghost is the explicit polylog closed form `2^(1-s) Li_s(u)`. -/
def conclusion_realinput40_even_defect_polylog_ghost_statement : Prop :=
  (∀ n : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_primitive_defect n u =
        atomPrimitiveCoeff n u) ∧
    (∀ n : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_ghost_defect n u =
        atomGhostCoeff n u) ∧
    (∀ n : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_primitive_defect n u =
        if n = 2 then u else 0) ∧
    (∀ n : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_ghost_defect n u =
        if Even n then (2 : ℂ) * u ^ (n / 2) else 0) ∧
    (∀ N : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_primitive_step N u =
        if 2 ≤ N then u else 0) ∧
    (∀ s : ℕ, ∀ u : ℂ,
      conclusion_realinput40_even_defect_polylog_ghost_dirichlet_series s u =
        ((2 : ℂ) / (2 : ℂ) ^ s) *
          conclusion_realinput40_even_defect_polylog_ghost_polylog s u) ∧
    (∀ s : ℕ,
      conclusion_realinput40_even_defect_polylog_ghost_dirichlet_series s 1 =
        ((2 : ℂ) / (2 : ℂ) ^ s) *
          conclusion_realinput40_even_defect_polylog_ghost_polylog s 1)

theorem paper_conclusion_realinput40_even_defect_polylog_ghost :
    conclusion_realinput40_even_defect_polylog_ghost_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n u
    rfl
  · intro n u
    rfl
  · intro n u
    have hatom :=
      paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate u 2 n
        (by norm_num)
    simpa [conclusion_realinput40_even_defect_polylog_ghost_primitive_defect] using hatom.2.1
  · intro n u
    have hatom :=
      paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate u 2 n
        (by norm_num)
    simpa [conclusion_realinput40_even_defect_polylog_ghost_ghost_defect] using hatom.1
  · intro N u
    have hprim :
        ∀ n : ℕ,
          conclusion_realinput40_even_defect_polylog_ghost_primitive_defect n u =
            if n = 2 then u else 0 := by
      intro n
      have hatom :=
        paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate u 2 n
          (by norm_num)
      simpa [conclusion_realinput40_even_defect_polylog_ghost_primitive_defect] using hatom.2.1
    by_cases hN : 2 ≤ N
    · rw [conclusion_realinput40_even_defect_polylog_ghost_primitive_step]
      calc
        Finset.sum (Finset.range (N + 1))
            (fun n => conclusion_realinput40_even_defect_polylog_ghost_primitive_defect n u) =
            Finset.sum (Finset.range (N + 1)) (fun n => if n = 2 then u else 0) := by
              simp [hprim]
        _ = u := by
              rw [Finset.sum_eq_single 2]
              · simp
              · intro n _ hn
                simp [hn]
              · intro hnotmem
                exfalso
                apply hnotmem
                exact Finset.mem_range.mpr (by omega)
        _ = if 2 ≤ N then u else 0 := by simp [hN]
    · have hcases : N = 0 ∨ N = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [conclusion_realinput40_even_defect_polylog_ghost_primitive_step, hprim, hN]
      · simp [conclusion_realinput40_even_defect_polylog_ghost_primitive_step, hprim, hN]
  · intro s u
    rfl
  · intro s
    rfl

end

end Omega.Conclusion
