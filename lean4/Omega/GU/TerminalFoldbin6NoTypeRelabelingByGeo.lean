import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- Paper-facing corollary: the geometric window-`6` involution preserves the BinFold type label
on every encoded word, so it induces no nontrivial relabeling on `X 6`.
    cor:terminal-foldbin6-no-type-relabeling-by-geo -/
theorem paper_terminal_foldbin6_no_type_relabeling_by_geo :
    (∀ n : Fin 64, Omega.cBinFold 6 (terminalFoldbin6GeoImage n.1) = Omega.cBinFold 6 n.1) ∧
      terminalFoldbin6GeoSwapFiberValues = [13, 16, 17, 20] := by
  rcases paper_terminal_foldbin6_two_point_fiber_direction_spectrum with
    ⟨_, _, hDir34, _, _, hSwap⟩
  refine ⟨?_, ?_⟩
  · have hGeo :
        ∀ n : Fin 64, Omega.cBinFold 6 (terminalFoldbin6GeoImage n.1) = Omega.cBinFold 6 n.1 := by
        native_decide
    exact hGeo
  · calc
      terminalFoldbin6GeoSwapFiberValues = terminalFoldbin6FiberValuesByDirection 34 := hSwap
      _ = [13, 16, 17, 20] := hDir34

end Omega.GU
