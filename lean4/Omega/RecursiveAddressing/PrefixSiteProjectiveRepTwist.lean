import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- A lightweight abstract Čech groupoid recording only which overlaps are available. -/
structure PrefixSiteCechGroupoid (ι : Type*) where
  overlap : ι → ι → Prop

/-- A minimal twisted linearization package: the multiplier is the only datum needed for the
projective-vs-strict comparison. -/
structure PrefixSiteTwistedAlgebra (ι : Type*) (A : Type*) where
  multiplier : ι → ι → ι → A

/-- The multiplier produced by a `1`-cochain adjustment. -/
def twoCoboundary {ι A : Type*} [AddCommGroup A] (η : ι → ι → A) : ι → ι → ι → A :=
  fun i j k => η i j + η j k - η i k

/-- Twisting the descent identifications by a `1`-cochain. -/
def adjustDescent {ι A : Type*} [AddCommGroup A] (ρ η : ι → ι → A) : ι → ι → A :=
  fun i j => ρ i j - η i j

/-- Projective descent data with multiplier `α`. -/
def IsProjectiveRep {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A) (ρ : ι → ι → A) : Prop :=
  ∀ ⦃i j k⦄, G.overlap i j → G.overlap j k → G.overlap i k →
    ρ i j + ρ j k = α i j k + ρ i k

/-- Strict descent data: composition is literal rather than projective. -/
def IsStrictRep {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (ρ : ι → ι → A) : Prop :=
  ∀ ⦃i j k⦄, G.overlap i j → G.overlap j k → G.overlap i k →
    ρ i j + ρ j k = ρ i k

/-- A projective representation strictifies if a `1`-cochain adjustment makes it strict. -/
def Strictifiable {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (ρ : ι → ι → A) : Prop :=
  ∃ η, IsStrictRep G (adjustDescent ρ η)

/-- The cocycle class is killed by a coboundary when the multiplier is the Čech coboundary of a
`1`-cochain on overlaps. -/
def MultiplierKilledByCoboundary {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A) : Prop :=
  ∃ η, ∀ ⦃i j k⦄, G.overlap i j → G.overlap j k → G.overlap i k →
    α i j k = twoCoboundary η i j k

theorem strictifiable_iff_killedByCoboundary {ι A : Type*} [AddCommGroup A]
    (G : PrefixSiteCechGroupoid ι) (α : ι → ι → ι → A) (ρ : ι → ι → A)
    (hρ : IsProjectiveRep G α ρ) :
    Strictifiable G ρ ↔ MultiplierKilledByCoboundary G α := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, ?_⟩
    intro i j k hij hjk hik
    have hproj := hρ hij hjk hik
    have hstrict := hη hij hjk hik
    have hstrictExpanded : (ρ i j - η i j) + (ρ j k - η j k) = ρ i k - η i k := by
      simpa [adjustDescent] using hstrict
    have hstrict' : ρ i j + ρ j k - ρ i k = η i j + η j k - η i k := by
      have hstrict0 : (ρ i j - η i j) + (ρ j k - η j k) - (ρ i k - η i k) = 0 := by
        rw [hstrictExpanded]
        abel
      apply sub_eq_zero.mp
      calc
        (ρ i j + ρ j k - ρ i k) - (η i j + η j k - η i k)
            = (ρ i j - η i j) + (ρ j k - η j k) - (ρ i k - η i k) := by
                abel
        _ = 0 := hstrict0
    calc
      α i j k = α i j k + ρ i k - ρ i k := by
        abel
      _ = ρ i j + ρ j k - ρ i k := by
        rw [← hproj]
      _ = η i j + η j k - η i k := hstrict'
      _ = twoCoboundary η i j k := rfl
  · rintro ⟨η, hη⟩
    refine ⟨η, ?_⟩
    intro i j k hij hjk hik
    have hproj := hρ hij hjk hik
    have hkill := hη hij hjk hik
    calc
      adjustDescent ρ η i j + adjustDescent ρ η j k
          = ρ i j + ρ j k - (η i j + η j k) := by
              simp [adjustDescent]
              abel
      _ = α i j k + ρ i k - (η i j + η j k) := by rw [hproj]
      _ = (η i j + η j k - η i k) + ρ i k - (η i j + η j k) := by
            simp [hkill, twoCoboundary]
      _ = ρ i k - η i k := by abel
      _ = adjustDescent ρ η i k := by simp [adjustDescent]

/-- Paper: `prop:prefix-site-projective-rep-twist`.
A Čech `2`-cocycle multiplier packages descent data as a projective representation of the overlap
groupoid, and strictification is equivalent to killing the multiplier by a coboundary
adjustment. -/
theorem paper_recursive_addressing_prefix_site_projective_rep_twist
    {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A) (ρ : ι → ι → A) (hρ : IsProjectiveRep G α ρ) :
    (∃ twisted : PrefixSiteTwistedAlgebra ι A, twisted.multiplier = α) ∧
      (Strictifiable G ρ ↔ MultiplierKilledByCoboundary G α) := by
  refine ⟨?_, strictifiable_iff_killedByCoboundary G α ρ hρ⟩
  exact ⟨⟨α⟩, rfl⟩

/-- Paper label: `prop:prefix-site-projective-rep-twist`. Strictification of a projective
representation is equivalent to killing its multiplier by a Čech coboundary. -/
theorem paper_prefix_site_projective_rep_twist
    {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A) (ρ : ι → ι → A) (hρ : IsProjectiveRep G α ρ) :
    Strictifiable G ρ ↔ MultiplierKilledByCoboundary G α := by
  exact strictifiable_iff_killedByCoboundary G α ρ hρ

end Omega.RecursiveAddressing
