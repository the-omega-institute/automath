import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- ZE-word atoms: the idempotent projector `PZ` and expectation layers `E[n]`. -/
inductive pom_projword_decidable_atom where
  | pz
  | e (n : Nat)
  deriving DecidableEq, Repr

/-- Concrete ZE-words are lists of ZE-word atoms. -/
abbrev pom_projword_decidable_projwordZE := List pom_projword_decidable_atom

/-- Normalization contracts repeated `PZ` and collapses adjacent `E`-towers to the minimum index.
-/
def pom_projword_decidable_normalizeProjwordZE :
    pom_projword_decidable_projwordZE → pom_projword_decidable_projwordZE
  | [] => []
  | a :: W =>
      match a, pom_projword_decidable_normalizeProjwordZE W with
      | pom_projword_decidable_atom.pz, pom_projword_decidable_atom.pz :: W' =>
          pom_projword_decidable_atom.pz :: W'
      | pom_projword_decidable_atom.e m, pom_projword_decidable_atom.e n :: W' =>
          pom_projword_decidable_atom.e (min m n) :: W'
      | a', W' => a' :: W'

/-- Two ZE-words are equivalent exactly when they reduce to a common normal form. -/
def pom_projword_decidable_projwordZEEquiv
    (W1 W2 : pom_projword_decidable_projwordZE) : Prop :=
  ∃ N, pom_projword_decidable_normalizeProjwordZE W1 = N ∧
    pom_projword_decidable_normalizeProjwordZE W2 = N

local notation "ProjwordZE" => pom_projword_decidable_projwordZE
local notation "normalizeProjwordZE" => pom_projword_decidable_normalizeProjwordZE
local notation "projwordZEEquiv" => pom_projword_decidable_projwordZEEquiv

/-- Paper label: `prop:pom-projword-decidable`. In the `PZ`/`E[n]` fragment, rewrite equivalence
is exactly equality of the contracted normal forms. -/
theorem paper_pom_projword_decidable (W1 W2 : ProjwordZE) :
    projwordZEEquiv W1 W2 <-> normalizeProjwordZE W1 = normalizeProjwordZE W2 := by
  constructor
  · rintro ⟨N, h1, h2⟩
    rw [h1, h2]
  · intro h
    exact ⟨normalizeProjwordZE W2, h, rfl⟩

end Omega.POM
