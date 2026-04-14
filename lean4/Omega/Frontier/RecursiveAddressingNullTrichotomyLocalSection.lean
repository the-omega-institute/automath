import Omega.Frontier.NullTrichotomyLocalSection

namespace Omega.Frontier.RecursiveAddressingNullTrichotomyLocalSection

open Omega.Topos

variable {α : Type*}

set_option maxHeartbeats 400000 in
/-- Publication wrapper for the recursive-addressing prefix-sites corollary on the finite-level
    trichotomy of address failure.
    cor:null-trichotomy-local-section -/
theorem paper_recursive_addressing_null_trichotomy_local_section
    (Adm LocSec CompSec Sec : α → Prop) (r : α)
    [Decidable (LocSec r)] [Decidable (CompSec r)]
    (hcompLoc : ∀ {x : α}, CompSec x → LocSec x)
    (hsecComp : ∀ {x : α}, Sec x → CompSec x) :
    Null Adm Sec r ↔
      ExactlyOne3
        (NullLoc Adm LocSec r)
        (NullCmp Adm LocSec CompSec r)
        (NullGlue Adm CompSec Sec r) :=
  Omega.Frontier.NullTrichotomyLocalSection.paper_null_trichotomy_local_section
    Adm LocSec CompSec Sec r hcompLoc hsecComp

end Omega.Frontier.RecursiveAddressingNullTrichotomyLocalSection
