import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- The signed geometric-stabilizer offset certificate extracted from the window-6 two-point
fiber spectrum. -/
def terminalWindow6GeometricStabilizerOffsets : Finset ℤ :=
  insert 0 <|
    (terminalFoldbin6TwoPointFiberDirectionSpectrum.image fun n : ℕ => (n : ℤ)) ∪
      (terminalFoldbin6TwoPointFiberDirectionSpectrum.image fun n : ℕ => -((n : ℤ)))

/-- The nonzero admissible local uplifts are exactly the signed geometric-stabilizer offsets whose
absolute values lie in the window-6 tail-offset set `{21, 34, 55}`. -/
def terminalWindow6NonzeroAdmissibleLocalUplifts : Finset ℤ :=
  (terminalWindow6GeometricStabilizerOffsets.erase 0).filter fun z =>
    z.natAbs ∈ terminalFoldbin6TailOffsets

/-- The full local uplift set includes the trivial offset together with the admissible nonzero
uplifts. -/
def terminalWindow6LocalUpliftSet : Finset ℤ :=
  insert 0 terminalWindow6NonzeroAdmissibleLocalUplifts

/-- Package the admissible window-6 local uplifts by intersecting the signed geometric-stabilizer
offset certificate with the tail-offset set `{21, 34, 55}`; the unique nonzero admissible uplift
is `±34`. -/
theorem paper_terminal_window6_local_uplift_admissibility :
    terminalWindow6LocalUpliftSet = ({0, 34, -34} : Finset ℤ) := by
  rcases paper_terminal_foldbin6_two_point_fiber_direction_spectrum with
    ⟨_, hSpectrum, _, _, _, _⟩
  rw [terminalWindow6LocalUpliftSet, terminalWindow6NonzeroAdmissibleLocalUplifts,
    terminalWindow6GeometricStabilizerOffsets, hSpectrum]
  decide

end Omega.GU
