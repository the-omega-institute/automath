import Omega.GU.TerminalFoldbin6StrongLumpabilityBinaryWitness
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- Paper-facing reduction of the minimal window-6 Markov obstruction to the explicit `F₈`
tail witness and the computed two-point direction spectrum.
    thm:window6-minimal-markov-obstruction-pure-f8-tail -/
theorem paper_window6_minimal_markov_obstruction_pure_f8_tail :
    terminalFoldbin6BinaryWitness 0 = 0 ∧
      terminalFoldbin6BinaryWitness 21 = 1 ∧
      21 = Nat.fib 8 ∧
      21 ∉ terminalFoldbin6TwoPointFiberDirectionSpectrum := by
  have h0 : terminalFoldbin6BinaryWitness 0 = 0 := by native_decide
  have h21 : terminalFoldbin6BinaryWitness 21 = 1 := by native_decide
  have hspectrum :
      terminalFoldbin6TwoPointFiberDirectionSpectrum = ({34, 38, 62} : Finset Nat) :=
    paper_terminal_foldbin6_two_point_fiber_direction_spectrum.2.1
  refine ⟨h0, h21, Omega.ZeckSig.fib_8_val.symm, ?_⟩
  have hnot : 21 ∉ ({34, 38, 62} : Finset Nat) := by native_decide
  simpa [hspectrum] using hnot

end Omega.GU
