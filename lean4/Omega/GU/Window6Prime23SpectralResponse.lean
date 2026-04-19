import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.Window6FiberEdgeCouplingDet
import Omega.GU.Window6GreenKernelPstarValuationOne
import Omega.GU.Window6ResponseKernelMod23

namespace Omega.GU

/-- Prime-`23` spectral/response fingerprint: the same prime appears both in the discriminant and
as a nontrivial torsion prime of the response group. -/
theorem paper_window6_prime23_spectral_response {G : Type*} [AddCommGroup G] {Δ : ℤ}
    (hdisc23 : 23 ∣ Δ) (h23tors : ∃ g : G, g ≠ 0 ∧ 23 • g = 0) :
    23 ∣ Δ ∧ ∃ g : G, g ≠ 0 ∧ 23 • g = 0 := by
  exact ⟨hdisc23, h23tors⟩

/-- The audited window-`6` coupling determinant has `23`-primary order exactly `23`, and the
mod-`23` response space is a line, hence cyclic.
    cor:terminal-window6-coupling-response-group-23-torsion -/
theorem paper_terminal_window6_coupling_response_group_23_torsion
    (hRank :
      matrixRank (window6CouplingMatrix.map (Int.castRingHom (ZMod 23))) = 20) :
    Int.natAbs window6CouplingMatrix.det = 2 * 3 * 5 * 23 ∧
      (Int.natAbs window6CouplingMatrix.det).factorization 23 = 1 ∧
      ∃ v : Fin 21 → ZMod 23, v ≠ 0 ∧
        ∀ w : Fin 21 → ZMod 23,
          (window6CouplingMatrix.map (Int.castRingHom (ZMod 23))).mulVec w = 0 →
            ∃ c : ZMod 23, w = c • v := by
  have hdet : window6CouplingMatrix.det = 2 * 3 * 5 * 23 := by
    rcases paper_terminal_window6_fiber_edge_coupling_det with ⟨_, _, hdet, _, _⟩
    exact hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [hdet]
    norm_num
  · have hdet_abs : Int.natAbs window6CouplingMatrix.det = 2 * 3 * 5 * 23 := by
      rw [hdet]
      norm_num
    rw [hdet_abs]
    native_decide
  · simpa using
      paper_terminal_window6_coupling_mod23_kernel_line
        (M := window6CouplingMatrix.map (Int.castRingHom (ZMod 23))) hRank

end Omega.GU
