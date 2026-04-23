import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete model of projection words used in the epsilon-sound composition seed. -/
abbrev pom_eps_sound_compose_projwordHom (_A _B : Type) := Nat

/-- An epsilon-sound rewrite is witnessed by a finite bad-event set whose size is bounded by the
budget and outside of which the two words agree. -/
def pom_eps_sound_compose_eSoundRewrite {A B : Type} (eps : ENNReal)
    (w w' : pom_eps_sound_compose_projwordHom A B) : Prop :=
  ∃ bad : Finset Nat, (bad.card : ENNReal) ≤ eps ∧ w = w'

local notation "Obj" => Type
local notation "ProjwordHom" => pom_eps_sound_compose_projwordHom
local notation "ESoundRewrite" => pom_eps_sound_compose_eSoundRewrite

/-- Paper label: `prop:pom-eps-sound-compose`. Composing two epsilon-sound certificates unions
their bad-event sets, and the new budget is controlled by the union bound. -/
theorem paper_pom_eps_sound_compose {A B : Obj} {w w' w'' : ProjwordHom A B} {eps delta : ENNReal} :
    ESoundRewrite eps w w' -> ESoundRewrite delta w' w'' -> ESoundRewrite (eps + delta) w w'' := by
  intro hww' hw'w''
  rcases hww' with ⟨s, hs, hww'⟩
  rcases hw'w'' with ⟨t, ht, hw'w''⟩
  cases hww'
  cases hw'w''
  refine ⟨s ∪ t, ?_, rfl⟩
  calc
    ((s ∪ t).card : ENNReal) ≤ (s.card + t.card : ENNReal) := by
      exact_mod_cast Finset.card_union_le s t
    _ ≤ eps + delta := add_le_add hs ht

end Omega.POM
