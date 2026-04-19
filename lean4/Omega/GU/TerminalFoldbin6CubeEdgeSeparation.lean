import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6OnebitErrorDetecting

namespace Omega.GU

/-- A window-6 one-bit hypercube edge always leaves the current `cBinFold` fiber, so each fiber is
an independent set in the cube graph.
    thm:terminal-foldbin6-cube-edge-separation -/
theorem paper_terminal_foldbin6_cube_edge_separation :
    (∀ {u v : Fin 64}, terminalFoldbin6CubeStep u v → cBinFold 6 u.1 ≠ cBinFold 6 v.1) ∧
      (∀ x : X 6, ∀ {u v : Fin 64}, cBinFold 6 u.1 = x → cBinFold 6 v.1 = x →
        hammingDist (intToWord 6 u.1) (intToWord 6 v.1) ≠ 1) := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact paper_terminal_foldbin6_onebit_error_detecting h
  · intro x u v hu hv hdist
    have hstep : terminalFoldbin6CubeStep u v := by
      simpa [terminalFoldbin6CubeStep] using hdist
    have hneq := paper_terminal_foldbin6_onebit_error_detecting hstep
    exact hneq (by rw [hu, hv])

end Omega.GU
