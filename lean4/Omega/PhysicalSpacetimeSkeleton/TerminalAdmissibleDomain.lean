import Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

namespace Omega.PhysicalSpacetimeSkeleton

universe u

open Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

/-- Concrete data for the terminal admissible-domain package attached to a fixed finite compatible
Lorentz family. -/
structure TerminalAdmissibleDomainData where
  ι : Type u
  instFintype : Fintype ι
  family : CompatibleLorentzFamily ι

attribute [instance] TerminalAdmissibleDomainData.instFintype

namespace TerminalAdmissibleDomainData

/-- The ambient disjoint union of local chart points. -/
abbrev chartPoint (D : TerminalAdmissibleDomainData) :=
  ChartPoint D.family

/-- The maximal admissible quotient domain for the fixed compatible chart family. -/
abbrev terminalDomain (D : TerminalAdmissibleDomainData) :=
  maximalAdmissibleDomain D.family

/-- A finite glued atlas over the fixed chart family is another quotient of the same disjoint
union, subject to a relation that only identifies genuinely overlapping chart points. -/
structure AdmissibleAtlas (D : TerminalAdmissibleDomainData) where
  rel : Setoid D.chartPoint
  rel_sub_overlap : ∀ {p q : D.chartPoint}, rel.r p q → (chartPointSetoid D.family).r p q

namespace AdmissibleAtlas

/-- The carrier of a finite glued atlas. -/
abbrev domain {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D) :=
  Quotient A.rel

/-- The local chart point viewed inside a glued atlas. -/
def point {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D)
    (i : D.ι) (x : D.family.Chart i) : A.domain :=
  Quotient.mk A.rel ⟨i, x⟩

/-- The canonical comparison map from a finite glued atlas to the maximal admissible quotient
domain. -/
def canonicalMap {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D) :
    A.domain → D.terminalDomain :=
  Quotient.lift
    (fun p : D.chartPoint => Quotient.mk (chartPointSetoid D.family) p)
    (fun _ _ h => Quotient.sound (A.rel_sub_overlap h))

lemma canonicalMap_point {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D)
    (i : D.ι) (x : D.family.Chart i) :
    A.canonicalMap (A.point i x) = pointClass D.family i x := by
  rfl

end AdmissibleAtlas

/-- The maximal admissible quotient domain is terminal when its glued metric is unique and every
other finite glued atlas admits a unique comparison map into it. -/
def isTerminal (D : TerminalAdmissibleDomainData) : Prop :=
  (∃! g : D.terminalDomain → ℝ, ∀ i x, g (pointClass D.family i x) = D.family.metric i x) ∧
    ∀ A : AdmissibleAtlas D,
      ∃! f : A.domain → D.terminalDomain, ∀ i x, f (A.point i x) = pointClass D.family i x

lemma unique_map_to_terminalDomain (D : TerminalAdmissibleDomainData) (A : AdmissibleAtlas D) :
    ∃! f : A.domain → D.terminalDomain, ∀ i x, f (A.point i x) = pointClass D.family i x := by
  refine ⟨A.canonicalMap, A.canonicalMap_point, ?_⟩
  intro f hf
  funext q
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨i, x⟩
  simpa [AdmissibleAtlas.point] using hf i x

end TerminalAdmissibleDomainData

open TerminalAdmissibleDomainData

/-- The maximal quotient domain of a finite compatible chart family is terminal among finite
glued atlases over that family: the descended metric is uniquely determined by the chart data, and
every other quotient atlas carries a unique comparison map into the maximal admissible quotient.
    thm:physical-spacetime-terminal-admissible-domain -/
theorem paper_physical_spacetime_terminal_admissible_domain
    (D : TerminalAdmissibleDomainData) : D.isTerminal := by
  refine ⟨?_, ?_⟩
  · simpa [TerminalAdmissibleDomainData.terminalDomain] using
      (paper_physical_spacetime_finite_compatible_family_glues D.family)
  · intro A
    exact D.unique_map_to_terminalDomain A

end Omega.PhysicalSpacetimeSkeleton
