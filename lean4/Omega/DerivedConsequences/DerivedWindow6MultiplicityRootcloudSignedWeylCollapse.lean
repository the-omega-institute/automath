import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6B3C3RootcloudIsotropicDesign

namespace Omega.DerivedConsequences

open Omega.GU

/-- The concrete window-`6` `B₃` root cloud used in the multiplicity collapse package. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_rootcloud : List Weight :=
  derived_window6_b3c3_rootcloud_isotropic_design_b3_roots

/-- The multiplicity-`2` layer: the unique short root `-e₁` together with the
four long roots in the plane `x₁ = 0`. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2_explicit : List Weight :=
  [(-1, 0, 0), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]

/-- The multiplicity-`3` layer: the four long roots in the plane `x₂ = 0`. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3_explicit : List Weight :=
  [(1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1)]

/-- The multiplicity-`4` layer: the remaining short roots together with the
four long roots in the plane `x₃ = 0`. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4_explicit : List Weight :=
  [(1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1), (1, 1, 0), (1, -1, 0),
    (-1, 1, 0), (-1, -1, 0)]

/-- The window-`6` multiplicity decorating the concrete `B₃` root cloud. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_multiplicity (α : Weight) : ℕ :=
  if α ∈ derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2_explicit then
    2
  else if α ∈ derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3_explicit then
    3
  else
    4

/-- The three multiplicity layers cut out from the concrete root cloud. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2 : List Weight :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_rootcloud.filter
    (fun α => derived_window6_multiplicity_rootcloud_signed_weyl_collapse_multiplicity α = 2)

def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3 : List Weight :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_rootcloud.filter
    (fun α => derived_window6_multiplicity_rootcloud_signed_weyl_collapse_multiplicity α = 3)

def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4 : List Weight :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_rootcloud.filter
    (fun α => derived_window6_multiplicity_rootcloud_signed_weyl_collapse_multiplicity α = 4)

/-- A signed Weyl element is a permutation code together with three sign bits. -/
structure derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl where
  permCode : Fin 6
  sign0 : Bool
  sign1 : Bool
  sign2 : Bool
deriving DecidableEq

/-- The six permutations of three coordinates, encoded as reorderings of `0,1,2`. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_permCoord
    (p : Fin 6) : Fin 3 → Fin 3 :=
  match p with
  | 0 => ![0, 1, 2]
  | 1 => ![0, 2, 1]
  | 2 => ![1, 0, 2]
  | 3 => ![1, 2, 0]
  | 4 => ![2, 0, 1]
  | 5 => ![2, 1, 0]

/-- Recover the sign attached to a coordinate. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signBit
    (g : derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl) :
    Fin 3 → Bool
  | 0 => g.sign0
  | 1 => g.sign1
  | 2 => g.sign2

/-- Coordinate projection from a weight. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_coord
    (α : Weight) : Fin 3 → ℤ
  | 0 => α.1
  | 1 => α.2.1
  | 2 => α.2.2

/-- Assemble a weight from its three coordinates. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_ofCoords
    (x : Fin 3 → ℤ) : Weight :=
  (x 0, x 1, x 2)

/-- Boolean sign bits interpreted as `±1`. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signValue (b : Bool) : ℤ :=
  cond b (-1) 1

/-- The signed-permutation action on the concrete `B₃` weight lattice. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_act
    (g : derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl)
    (α : Weight) : Weight :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_ofCoords fun i =>
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signValue
        (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signBit g i) *
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_coord α
        (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_permCoord g.permCode i)

/-- The surviving Klein-four subgroup consists of the identity permutation
with free sign choices on the second and third coordinates only. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diag
    (ε₂ ε₃ : Bool) :
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl where
  permCode := 0
  sign0 := false
  sign1 := ε₂
  sign2 := ε₃

/-- All `48 = 6 · 2³` signed Weyl elements. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allSignedWeyl :
    List derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl :=
  ([0, 1, 2, 3, 4, 5] : List (Fin 6)).flatMap fun p =>
    ([false, true] : List Bool).flatMap fun s0 =>
      ([false, true] : List Bool).flatMap fun s1 =>
        ([false, true] : List Bool).map fun s2 =>
          { permCode := p, sign0 := s0, sign1 := s1, sign2 := s2 }

/-- Boolean layer-preservation test on a finite root list. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
    (roots : List Weight)
    (g : derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl) : Bool :=
  roots.all fun α =>
    decide
      (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_act g α ∈ roots)

/-- The collapse condition checked on one signed Weyl element. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_collapseCheck
    (g : derived_window6_multiplicity_rootcloud_signed_weyl_collapse_signedWeyl) : Bool :=
  !(derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
        derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2 g &&
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
        derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3 g &&
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
        derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4 g) ||
    decide
      (g.permCode = 0 ∧ g.sign0 = false ∧
        derived_window6_multiplicity_rootcloud_signed_weyl_collapse_act g (1, 0, 0) = (1, 0, 0) ∧
          derived_window6_multiplicity_rootcloud_signed_weyl_collapse_act g (-1, 0, 0) = (-1, 0, 0))

/-- The four diagonal sign choices all preserve the three multiplicity layers. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diagCheck
    (ε₂ ε₃ : Bool) : Bool :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
        derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2
        (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diag ε₂ ε₃) &&
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
          derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3
          (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diag ε₂ ε₃) &&
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_preserves
            derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4
            (derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diag ε₂ ε₃)

/-- Exhaustive boolean audit over all `48` signed Weyl elements. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allCollapseChecks : Bool :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allSignedWeyl.all
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_collapseCheck

/-- Exhaustive boolean audit over the four surviving diagonal sign choices. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allDiagChecks : Bool :=
  ([false, true] : List Bool).all fun ε₂ =>
    ([false, true] : List Bool).all fun ε₃ =>
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_diagCheck ε₂ ε₃

/-- Concrete statement of the signed-Weyl collapse for the multiplicity-decorated
window-`6` `B₃` root cloud. -/
def derived_window6_multiplicity_rootcloud_signed_weyl_collapse_statement : Prop :=
  derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2 =
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R2_explicit ∧
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3 =
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R3_explicit ∧
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4 =
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_R4_explicit ∧
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allCollapseChecks = true ∧
      derived_window6_multiplicity_rootcloud_signed_weyl_collapse_allDiagChecks = true

/-- Paper label: `cor:derived-window6-multiplicity-rootcloud-signed-weyl-collapse`. The three
multiplicity layers are the concrete `R₂/R₃/R₄` root subsets, and a finite signed-permutation
check shows that any signed Weyl symmetry preserving all three layers is forced into the Klein
four subgroup `diag(1, ε₂, ε₃)`. -/
theorem paper_derived_window6_multiplicity_rootcloud_signed_weyl_collapse :
    derived_window6_multiplicity_rootcloud_signed_weyl_collapse_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.DerivedConsequences
