import Omega.GU.TerminalWindow6LocalUpliftAdmissibility

namespace Omega.GU

/-- Paper-facing wrapper: the window-`6` local-uplift certificate is implementation-independent
for the icosahedral prototype interface, so the only admissible offsets are `0` and `±34`.
    cor:bdry-delta34-universal-icosahedral-local-uplift -/
theorem paper_bdry_delta34_universal_icosahedral_local_uplift :
    terminalWindow6LocalUpliftSet = ({0, 34, -34} : Finset ℤ) := by
  simpa using paper_terminal_window6_local_uplift_admissibility

end Omega.GU
