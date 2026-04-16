import Mathlib.Data.Set.Basic
import Omega.Topos.NullTrichotomy

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the branched-gerbe semantics of gluing-level
    absence.
    thm:gerbe-null-semantics -/
theorem paper_gluing_failure_gerbe_null_semantics
    {Ref Branch : Type}
    (Adm CompSec Sec : Ref → Prop)
    (Visible : Ref → Set Branch)
    (Neutral Obstructed : Ref → Branch → Prop)
    {r : Ref}
    (hAdm : Adm r)
    (hComp : CompSec r ↔ Set.Nonempty (Visible r))
    (hSec : Sec r ↔ ∃ v, v ∈ Visible r ∧ Neutral r v)
    (hDerived :
      ∀ v, v ∈ Visible r → (¬ Neutral r v ↔ Obstructed r v)) :
    (CompSec r ↔ Set.Nonempty (Visible r)) ∧
      (Sec r ↔ ∃ v, v ∈ Visible r ∧ Neutral r v) ∧
      (NullGlue Adm CompSec Sec r ↔
        Set.Nonempty (Visible r) ∧
          ∀ v, v ∈ Visible r → ¬ Neutral r v) ∧
      (NullGlue Adm CompSec Sec r ↔
        Set.Nonempty (Visible r) ∧
          ∀ v, v ∈ Visible r → Obstructed r v) := by
  have hNullGlue :
      NullGlue Adm CompSec Sec r ↔
        Set.Nonempty (Visible r) ∧
          ∀ v, v ∈ Visible r → ¬ Neutral r v := by
    constructor
    · rintro ⟨_, hCompR, hNotSec⟩
      refine ⟨hComp.mp hCompR, ?_⟩
      intro v hv hNeutral
      exact hNotSec (hSec.mpr ⟨v, hv, hNeutral⟩)
    · rintro ⟨hVisible, hNoNeutral⟩
      refine ⟨hAdm, hComp.mpr hVisible, ?_⟩
      intro hSecR
      rcases hSec.mp hSecR with ⟨v, hv, hNeutral⟩
      exact hNoNeutral v hv hNeutral
  refine ⟨hComp, hSec, ?_, ?_⟩
  · exact hNullGlue
  · constructor
    · intro hNull
      rcases hNullGlue.mp hNull with ⟨hVisible, hNoNeutral⟩
      refine ⟨hVisible, ?_⟩
      intro v hv
      exact (hDerived v hv).mp (hNoNeutral v hv)
    · rintro ⟨hVisible, hObstructed⟩
      refine hNullGlue.mpr ⟨hVisible, ?_⟩
      intro v hv
      exact (hDerived v hv).mpr (hObstructed v hv)

end Omega.Topos
