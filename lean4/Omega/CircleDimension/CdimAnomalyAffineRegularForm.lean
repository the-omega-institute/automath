import Mathlib.Tactic

namespace Omega.CircleDimension

section

variable {A0 D A : Type*} [AddCommGroup A0] [AddCommGroup D] [AddCommGroup A]

/-- The local product coordinate map attached to a splitting section. -/
def anomalyAffineRegularFormPhi (ι : A0 →+ A) (s : D →+ A) : A0 × D →+ A where
  toFun z := ι z.1 + s z.2
  map_zero' := by simp
  map_add' := by
    intro z w
    rcases z with ⟨a, d⟩
    rcases w with ⟨a', d'⟩
    simp [map_add, add_assoc, add_left_comm, add_comm]

/-- Changing the splitting by `h` translates only the `A0`-coordinate. -/
def anomalyAffineRegularFormShift (h : D →+ A0) : A0 × D →+ A0 × D where
  toFun z := (z.1 + h z.2, z.2)
  map_zero' := by simp
  map_add' := by
    intro z w
    rcases z with ⟨a, d⟩
    rcases w with ⟨a', d'⟩
    simp [map_add, add_assoc, add_left_comm, add_comm]

/-- The shifted section `s' = s + h`, viewed inside `A` through the kernel inclusion `ι`. -/
def anomalyShiftedSection (ι : A0 →+ A) (s : D →+ A) (h : D →+ A0) : D →+ A where
  toFun d := ι (h d) + s d
  map_zero' := by simp
  map_add' := by
    intro d d'
    simp [map_add, add_assoc, add_left_comm, add_comm]

theorem anomalyAffineRegularForm_kernel_trivial
    (ι : A0 →+ A) (π : A →+ D) (s : D →+ A) (hπι : ∀ a0, π (ι a0) = 0)
    (hπs : Function.LeftInverse π s) (hinj : Function.Injective ι) :
    ∀ z : A0 × D, anomalyAffineRegularFormPhi ι s z = 0 → z = 0 := by
  rintro ⟨a, d⟩ hz
  have hproj := congrArg π hz
  have hd : d = 0 := by
    calc
      d = π (s d) := by symm; exact hπs d
      _ = π (ι a + s d) := by rw [map_add, hπι a, zero_add]
      _ = 0 := by simpa [anomalyAffineRegularFormPhi] using hproj
  have ha0 : ι a = 0 := by
    simpa [anomalyAffineRegularFormPhi, hd] using hz
  have ha : a = 0 := by
    apply hinj
    simpa using ha0
  simp [ha, hd]

theorem anomalyAffineRegularForm_injective
    (ι : A0 →+ A) (π : A →+ D) (s : D →+ A) (hπι : ∀ a0, π (ι a0) = 0)
    (hπs : Function.LeftInverse π s) (hinj : Function.Injective ι) :
    Function.Injective (anomalyAffineRegularFormPhi ι s) := by
  intro z w hzw
  rcases z with ⟨a, d⟩
  rcases w with ⟨a', d'⟩
  have hproj := congrArg π hzw
  have hd : d = d' := by
    calc
      d = π (s d) := by symm; exact hπs d
      _ = π (ι a + s d) := by rw [map_add, hπι a, zero_add]
      _ = π (ι a' + s d') := by simpa [anomalyAffineRegularFormPhi] using hproj
      _ = π (s d') := by rw [map_add, hπι a', zero_add]
      _ = d' := hπs d'
  have haι : ι a = ι a' := by
    simpa [anomalyAffineRegularFormPhi, hd] using hzw
  have ha : a = a' := hinj haι
  simp [ha, hd]

theorem anomalyAffineRegularForm_surjective
    (ι : A0 →+ A) (π : A →+ D) (s : D →+ A)
    (hdecomp : ∀ x : A, ∃ a0 : A0, x = ι a0 + s (π x)) :
    Function.Surjective (anomalyAffineRegularFormPhi ι s) := by
  intro x
  rcases hdecomp x with ⟨a0, ha0⟩
  exact ⟨(a0, π x), by simpa [anomalyAffineRegularFormPhi] using ha0.symm⟩

theorem anomalyAffineRegularForm_coordinate_change
    (ι : A0 →+ A) (s : D →+ A) (h : D →+ A0) :
    anomalyAffineRegularFormPhi ι (anomalyShiftedSection ι s h) =
      (anomalyAffineRegularFormPhi ι s).comp (anomalyAffineRegularFormShift h) := by
  ext z
  rcases z with ⟨a, d⟩
  simp [anomalyAffineRegularFormPhi, anomalyAffineRegularFormShift, anomalyShiftedSection,
    add_assoc]

/-- Paper label: `thm:cdim-anomaly-affine-regular-form`. Fixing a splitting section `s` identifies
the ambient anomaly group with the product of the kernel coordinate and the defect coordinate, and
shifting the section by `h` acts by the affine coordinate change `(a, d) ↦ (a + h d, d)`. -/
theorem paper_cdim_anomaly_affine_regular_form
    (ι : A0 →+ A) (π : A →+ D) (s : D →+ A) (hπι : ∀ a0, π (ι a0) = 0)
    (hπs : Function.LeftInverse π s)
    (hdecomp : ∀ x : A, ∃ a0 : A0, x = ι a0 + s (π x))
    (hinj : Function.Injective ι) :
    let Φs := anomalyAffineRegularFormPhi ι s
    (∀ z, Φs z = 0 → z = 0) ∧
      Function.Surjective Φs ∧
      Function.Bijective Φs ∧
      (∀ h : D →+ A0,
        anomalyAffineRegularFormPhi ι (anomalyShiftedSection ι s h) =
          Φs.comp (anomalyAffineRegularFormShift h)) := by
  dsimp
  have hker := anomalyAffineRegularForm_kernel_trivial ι π s hπι hπs hinj
  have hsurj := anomalyAffineRegularForm_surjective ι π s hdecomp
  have hinjective := anomalyAffineRegularForm_injective ι π s hπι hπs hinj
  refine ⟨hker, hsurj, ⟨hinjective, hsurj⟩, ?_⟩
  intro h
  exact anomalyAffineRegularForm_coordinate_change ι s h

end

end Omega.CircleDimension
