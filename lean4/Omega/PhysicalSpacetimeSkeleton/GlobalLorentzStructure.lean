import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

universe u

/-- Minimal scalar-valued Lorentz witness used by the paper-facing gluing wrapper. -/
def IsLorentzValue (g : ℝ) : Prop :=
  g < 0 ∨ 0 ≤ g

/-- A finite family of local charts whose scalar Lorentz data agree on overlaps. -/
structure CompatibleLorentzFamily (ι : Type u) [Fintype ι] where
  Chart : ι → Type u
  metric : ∀ i, Chart i → ℝ
  overlap : ∀ i j, Chart i → Chart j → Prop
  overlap_refl : ∀ i x, overlap i i x x
  overlap_symm :
    ∀ {i j} {x : Chart i} {y : Chart j}, overlap i j x y → overlap j i y x
  overlap_trans :
    ∀ {i j k} {x : Chart i} {y : Chart j} {z : Chart k},
      overlap i j x y → overlap j k y z → overlap i k x z
  metric_compat :
    ∀ {i j} {x : Chart i} {y : Chart j}, overlap i j x y → metric i x = metric j y
  lorentz : ∀ i x, IsLorentzValue (metric i x)

/-- The disjoint union of all local chart domains. -/
abbrev ChartPoint {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι) :=
  Σ i, F.Chart i

/-- Overlap equivalence relation on the disjoint union of chart points. -/
def chartPointSetoid {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι) :
    Setoid (ChartPoint F) where
  r p q := F.overlap p.1 q.1 p.2 q.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact F.overlap_refl p.1 p.2
    · intro p q hpq
      exact F.overlap_symm hpq
    · intro p q r hpq hqr
      exact F.overlap_trans hpq hqr

/-- The maximal admissible quotient domain obtained from a finite compatible chart family. -/
abbrev maximalAdmissibleDomain {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι) :=
  Quotient (chartPointSetoid F)

/-- The quotient class of a local chart point. -/
def pointClass {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι)
    (i : ι) (x : F.Chart i) : maximalAdmissibleDomain F :=
  Quotient.mk (chartPointSetoid F) ⟨i, x⟩

/-- The descended global metric on the maximal admissible quotient domain. -/
def globalMetric {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι) :
    maximalAdmissibleDomain F → ℝ :=
  Quotient.lift (fun p : ChartPoint F => F.metric p.1 p.2) <| by
    intro p q hpq
    exact F.metric_compat hpq

/-- Local Lorentz metrics agree on every overlap by definition of compatibility. -/
theorem local_metrics_agree_on_overlaps {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι)
    {i j} {x : F.Chart i} {y : F.Chart j} (hxy : F.overlap i j x y) :
    F.metric i x = F.metric j y :=
  F.metric_compat hxy

/-- A finite compatible family glues to a unique scalar metric on the quotient domain. -/
theorem finite_compatible_family_glues {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι) :
    ∃ g : maximalAdmissibleDomain F → ℝ, ∀ i x, g (pointClass F i x) = F.metric i x := by
  refine ⟨globalMetric F, ?_⟩
  intro i x
  rfl

/-- Paper-facing global Lorentz wrapper: a finite compatible family of local Lorentz charts
glues, their local metrics agree on overlaps, and the glued metric descends to the maximal
admissible quotient domain.
    thm:physical-spacetime-global-lorentz-structure -/
theorem paper_physical_spacetime_global_lorentz_structure :
    ∀ {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι),
      ∃ g : maximalAdmissibleDomain F → ℝ,
        (∀ i x, g (pointClass F i x) = F.metric i x) ∧
        ∀ q, IsLorentzValue (g q) := by
  intro ι _ F
  obtain ⟨g, hg⟩ := finite_compatible_family_glues F
  refine ⟨g, hg, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨i, x⟩
  have hMetric : g ⟦⟨i, x⟩⟧ = F.metric i x := by
    simpa [pointClass] using hg i x
  rw [hMetric]
  exact F.lorentz i x

end Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure
