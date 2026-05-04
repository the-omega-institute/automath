import Omega.GU.Window6Prime23SpectralResponse

namespace Omega.Conclusion

open Omega.GU

/-- Paper label: `thm:conclusion-window6-canonical-oddprime-response-line`. -/
theorem paper_conclusion_window6_canonical_oddprime_response_line
    (hRank :
      matrixRank (Omega.GU.window6CouplingMatrix.map (Int.castRingHom (ZMod 23))) = 20) :
    Int.natAbs Omega.GU.window6CouplingMatrix.det = 2 * 3 * 5 * 23 ∧
      (Int.natAbs Omega.GU.window6CouplingMatrix.det).factorization 23 = 1 ∧
      ∃ v : Fin 21 → ZMod 23, v ≠ 0 ∧
        ∀ w : Fin 21 → ZMod 23,
          (Omega.GU.window6CouplingMatrix.map (Int.castRingHom (ZMod 23))).mulVec w = 0 →
            ∃ c : ZMod 23, w = c • v := by
  simpa using Omega.GU.paper_terminal_window6_coupling_response_group_23_torsion hRank

end Omega.Conclusion
