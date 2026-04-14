import Omega.Topos.NullTrichotomy

namespace Omega.Frontier.NullTrichotomyLocalSection

open Omega.Topos

variable {α : Type*}

/-- Paper wrapper for the local-section version of the null trichotomy.
    cor:null-trichotomy-local-section -/
theorem paper_null_trichotomy_local_section
    (Adm LocSec CompSec Sec : α → Prop) (r : α)
    [Decidable (LocSec r)] [Decidable (CompSec r)]
    (hcompLoc : ∀ {x : α}, CompSec x → LocSec x)
    (hsecComp : ∀ {x : α}, Sec x → CompSec x) :
    Null Adm Sec r ↔
      ExactlyOne3
        (NullLoc Adm LocSec r)
        (NullCmp Adm LocSec CompSec r)
        (NullGlue Adm CompSec Sec r) :=
  Omega.Topos.paper_null_trichotomy_seeds Adm LocSec CompSec Sec r hcompLoc hsecComp

end Omega.Frontier.NullTrichotomyLocalSection
