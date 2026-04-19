import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.GU

instance : Fact (Nat.Prime 23) := ⟨by decide⟩

noncomputable abbrev matrixRank {m n : Type*} [Fintype m] [Fintype n] {R : Type*} [Field R]
    (M : Matrix m n R) : ℕ :=
  M.rank

theorem paper_terminal_window6_coupling_mod23_kernel_line
    (M : Matrix (Fin 21) (Fin 21) (ZMod 23)) (hRank : matrixRank M = 20) :
    ∃ v : Fin 21 → ZMod 23, v ≠ 0 ∧
      ∀ w : Fin 21 → ZMod 23, M.mulVec w = 0 → ∃ c : ZMod 23, w = c • v := by
  have hker_finrank :
      Module.finrank (ZMod 23) (LinearMap.ker M.mulVecLin) = 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (K := ZMod 23) (f := M.mulVecLin)
    have hrange : Module.finrank (ZMod 23) (LinearMap.range M.mulVecLin) = 20 := by
      simpa [matrixRank, Matrix.rank] using hRank
    rw [hrange, Module.finrank_pi, Fintype.card_fin] at hsum
    omega
  have hker_ne_bot : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    exact Submodule.one_le_finrank_iff.mp (by simpa [hker_finrank])
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hker_ne_bot
  let vK : LinearMap.ker M.mulVecLin := ⟨v, hv_mem⟩
  have hvK_ne : vK ≠ 0 := by
    intro hvK_zero
    apply hv_ne
    exact congrArg Subtype.val hvK_zero
  have hspan :
      ∀ wK : LinearMap.ker M.mulVecLin, ∃ c : ZMod 23, c • vK = wK :=
    fun wK => exists_smul_eq_of_finrank_eq_one hker_finrank hvK_ne wK
  refine ⟨v, hv_ne, ?_⟩
  intro w hw
  let wK : LinearMap.ker M.mulVecLin := ⟨w, by simpa using hw⟩
  rcases hspan wK with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  exact (congrArg Subtype.val hc).symm

end Omega.GU
