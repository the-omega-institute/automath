import Mathlib.Tactic
import Omega.CircleDimension.CdimAnomalyAffineRegularForm

namespace Omega.CircleDimension

section

variable {A0 D : Type*} [AddCommGroup A0] [AddCommGroup D]

/-- The canonical splitting associated to a homomorphism `h : D → A0`. -/
def cdim_anomaly_splitting_torsor_obstruction_sectionFromHom (h : D →+ A0) :
    D →+ A0 × D where
  toFun d := (h d, d)
  map_zero' := by simp
  map_add' := by
    intro d e
    simp [map_add]

/-- A section of the anomaly projection is characterized pointwise on the defect coordinate. -/
def cdim_anomaly_splitting_torsor_obstruction_isSplitting (s : D →+ A0 × D) : Prop :=
  ∀ d, (s d).2 = d

/-- First coordinate of a splitting section. -/
def cdim_anomaly_splitting_torsor_obstruction_head (s : D →+ A0 × D) : D →+ A0 where
  toFun d := (s d).1
  map_zero' := by simp
  map_add' := by
    intro d e
    simp [map_add]

/-- Difference of two sections, valued in the kernel coordinate. -/
def cdim_anomaly_splitting_torsor_obstruction_difference (s t : D →+ A0 × D) : D →+ A0 where
  toFun d := (t d).1 - (s d).1
  map_zero' := by simp
  map_add' := by
    intro d e
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Translating a section by a kernel-valued homomorphism. -/
def cdim_anomaly_splitting_torsor_obstruction_translate (h : D →+ A0) (s : D →+ A0 × D) :
    D →+ A0 × D where
  toFun d := ((s d).1 + h d, (s d).2)
  map_zero' := by simp
  map_add' := by
    intro d e
    simp [map_add, add_assoc, add_left_comm, add_comm]

/-- Pullback defect for a chosen automorphism pair on kernel and defect coordinates. -/
def cdim_anomaly_splitting_torsor_obstruction_cocycle
    (α0 : A0 ≃+ A0) (αD : D ≃+ D) (h : D →+ A0) : D →+ A0 where
  toFun d := α0 (h d) - h (αD d)
  map_zero' := by simp
  map_add' := by
    intro d e
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Invariance of a splitting under the induced pullback action. -/
def cdim_anomaly_splitting_torsor_obstruction_invariant
    (α0 : A0 ≃+ A0) (αD : D ≃+ D) (s : D →+ A0 × D) : Prop :=
  cdim_anomaly_splitting_torsor_obstruction_isSplitting s ∧
    ∀ d, α0 ((s d).1) = (s (αD d)).1

private lemma cdim_anomaly_splitting_torsor_obstruction_section_isSplitting (h : D →+ A0) :
    cdim_anomaly_splitting_torsor_obstruction_isSplitting
      (cdim_anomaly_splitting_torsor_obstruction_sectionFromHom h) := by
  intro d
  simp [cdim_anomaly_splitting_torsor_obstruction_sectionFromHom]

private lemma cdim_anomaly_splitting_torsor_obstruction_section_head
    (s : D →+ A0 × D)
    (hs : cdim_anomaly_splitting_torsor_obstruction_isSplitting s) :
    cdim_anomaly_splitting_torsor_obstruction_sectionFromHom
        (cdim_anomaly_splitting_torsor_obstruction_head s) = s := by
  ext d <;> simp [cdim_anomaly_splitting_torsor_obstruction_sectionFromHom,
    cdim_anomaly_splitting_torsor_obstruction_head, hs d]

private lemma cdim_anomaly_splitting_torsor_obstruction_translate_isSplitting
    (h : D →+ A0) (s : D →+ A0 × D)
    (hs : cdim_anomaly_splitting_torsor_obstruction_isSplitting s) :
    cdim_anomaly_splitting_torsor_obstruction_isSplitting
      (cdim_anomaly_splitting_torsor_obstruction_translate h s) := by
  intro d
  simpa [cdim_anomaly_splitting_torsor_obstruction_translate] using hs d

private lemma cdim_anomaly_splitting_torsor_obstruction_translate_difference
    (s t : D →+ A0 × D)
    (hs : cdim_anomaly_splitting_torsor_obstruction_isSplitting s)
    (ht : cdim_anomaly_splitting_torsor_obstruction_isSplitting t) :
    cdim_anomaly_splitting_torsor_obstruction_translate
        (cdim_anomaly_splitting_torsor_obstruction_difference s t) s = t := by
  ext d <;> simp [cdim_anomaly_splitting_torsor_obstruction_translate,
    cdim_anomaly_splitting_torsor_obstruction_difference, hs d, ht d, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

private lemma cdim_anomaly_splitting_torsor_obstruction_translate_unique
    (s t : D →+ A0 × D)
    (h k : D →+ A0)
    (hh : cdim_anomaly_splitting_torsor_obstruction_translate h s = t)
    (hk : cdim_anomaly_splitting_torsor_obstruction_translate k s = t) :
    h = k := by
  ext d
  have hh' : (s d).1 + h d = (t d).1 := by
    simpa [cdim_anomaly_splitting_torsor_obstruction_translate] using
      congrArg (fun f : D →+ A0 × D => (f d).1) hh
  have hk' : (s d).1 + k d = (t d).1 := by
    simpa [cdim_anomaly_splitting_torsor_obstruction_translate] using
      congrArg (fun f : D →+ A0 × D => (f d).1) hk
  exact add_left_cancel (hh'.trans hk'.symm)

private lemma cdim_anomaly_splitting_torsor_obstruction_cocycle_zero_iff
    (α0 : A0 ≃+ A0) (αD : D ≃+ D) (h : D →+ A0) :
    cdim_anomaly_splitting_torsor_obstruction_cocycle α0 αD h = 0 ↔
      cdim_anomaly_splitting_torsor_obstruction_invariant α0 αD
        (cdim_anomaly_splitting_torsor_obstruction_sectionFromHom h) := by
  constructor
  · intro hc
    refine ⟨cdim_anomaly_splitting_torsor_obstruction_section_isSplitting h, ?_⟩
    intro d
    have hd := congrArg (fun f : D →+ A0 => f d) hc
    exact sub_eq_zero.mp (by simpa [cdim_anomaly_splitting_torsor_obstruction_cocycle] using hd)
  · rintro ⟨hs, hinv⟩
    ext d
    exact sub_eq_zero.mpr (by simpa [cdim_anomaly_splitting_torsor_obstruction_sectionFromHom] using hinv d)

/-- Paper label: `prop:cdim-anomaly-splitting-torsor-obstruction`.
In the affine-regular-form model `A0 × D`, splittings are exactly kernel-valued sections; they form
a free transitive torsor under `Hom(D, A0)`, and the pullback defect cocycle vanishes exactly when
an invariant splitting exists. -/
theorem paper_cdim_anomaly_splitting_torsor_obstruction
    (α0 : A0 ≃+ A0) (αD : D ≃+ D) :
    (∃ s : D →+ A0 × D,
      cdim_anomaly_splitting_torsor_obstruction_isSplitting s) ∧
      (∀ s t : D →+ A0 × D,
        cdim_anomaly_splitting_torsor_obstruction_isSplitting s →
          cdim_anomaly_splitting_torsor_obstruction_isSplitting t →
            ∃! h : D →+ A0,
              cdim_anomaly_splitting_torsor_obstruction_translate h s = t) ∧
      (∀ h : D →+ A0,
        cdim_anomaly_splitting_torsor_obstruction_isSplitting
          (cdim_anomaly_splitting_torsor_obstruction_sectionFromHom h)) ∧
      (∀ s : D →+ A0 × D,
        cdim_anomaly_splitting_torsor_obstruction_isSplitting s →
          cdim_anomaly_splitting_torsor_obstruction_sectionFromHom
              (cdim_anomaly_splitting_torsor_obstruction_head s) = s) ∧
      (∀ h : D →+ A0,
        cdim_anomaly_splitting_torsor_obstruction_cocycle α0 αD h = 0 ↔
          cdim_anomaly_splitting_torsor_obstruction_invariant α0 αD
            (cdim_anomaly_splitting_torsor_obstruction_sectionFromHom h)) ∧
      ((∃ s : D →+ A0 × D,
          cdim_anomaly_splitting_torsor_obstruction_invariant α0 αD s) ↔
        ∃ h : D →+ A0,
          cdim_anomaly_splitting_torsor_obstruction_cocycle α0 αD h = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨cdim_anomaly_splitting_torsor_obstruction_sectionFromHom 0,
      cdim_anomaly_splitting_torsor_obstruction_section_isSplitting 0⟩
  · intro s t hs ht
    refine ⟨cdim_anomaly_splitting_torsor_obstruction_difference s t, ?_, ?_⟩
    · exact cdim_anomaly_splitting_torsor_obstruction_translate_difference s t hs ht
    · intro h hh
      exact cdim_anomaly_splitting_torsor_obstruction_translate_unique s t h
        (cdim_anomaly_splitting_torsor_obstruction_difference s t) hh
        (cdim_anomaly_splitting_torsor_obstruction_translate_difference s t hs ht)
  · intro h
    exact cdim_anomaly_splitting_torsor_obstruction_section_isSplitting h
  · intro s hs
    exact cdim_anomaly_splitting_torsor_obstruction_section_head s hs
  · intro h
    exact cdim_anomaly_splitting_torsor_obstruction_cocycle_zero_iff α0 αD h
  · constructor
    · rintro ⟨s, hs⟩
      refine ⟨cdim_anomaly_splitting_torsor_obstruction_head s, ?_⟩
      have hsection :
          cdim_anomaly_splitting_torsor_obstruction_sectionFromHom
              (cdim_anomaly_splitting_torsor_obstruction_head s) = s :=
        cdim_anomaly_splitting_torsor_obstruction_section_head s hs.1
      rw [cdim_anomaly_splitting_torsor_obstruction_cocycle_zero_iff α0 αD]
      rw [hsection]
      exact hs
    · rintro ⟨h, hh⟩
      exact ⟨cdim_anomaly_splitting_torsor_obstruction_sectionFromHom h,
        (cdim_anomaly_splitting_torsor_obstruction_cocycle_zero_iff α0 αD h).mp hh⟩

end

end Omega.CircleDimension
