import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-s3-double-cover-branch-complementarity`. -/
theorem paper_xi_terminal_zm_s3_double_cover_branch_complementarity {Point : Type}
    (qBranch piUnramified sixPointSupport : Point → Prop)
    (hbranch : ∀ Q, Iff (qBranch Q) (sixPointSupport Q))
    (hcomp : ∀ Q, Iff (sixPointSupport Q) (piUnramified Q)) :
    ∀ Q, Iff (qBranch Q) (piUnramified Q) := by
  intro Q
  constructor
  · intro hq
    exact (hcomp Q).mp ((hbranch Q).mp hq)
  · intro hπ
    exact (hbranch Q).mpr ((hcomp Q).mpr hπ)

end Omega.Zeta
