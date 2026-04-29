import Mathlib.Tactic

namespace Omega.Conclusion

universe u v w

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
structure conclusion_relation_groupoid_reduction_zp_data where
  Omega : Type u
  X : Type v
  Zp : Type w
  zpAddCommGroup : AddCommGroup Zp
  f : Omega → X
  r : Omega → Zp
  iota_injective : Function.Injective fun omega : Omega => (f omega, r omega)

namespace conclusion_relation_groupoid_reduction_zp_data

attribute [instance] zpAddCommGroup

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_iota
    (D : conclusion_relation_groupoid_reduction_zp_data) (omega : D.Omega) : D.X × D.Zp :=
  (D.f omega, D.r omega)

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
@[ext]
structure conclusion_relation_groupoid_reduction_zp_relation_arrow
    (D : conclusion_relation_groupoid_reduction_zp_data) where
  source : D.Omega
  target : D.Omega
  same_base : D.f source = D.f target

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
@[ext]
structure conclusion_relation_groupoid_reduction_zp_reduced_action_arrow
    (D : conclusion_relation_groupoid_reduction_zp_data) where
  sourcePoint : D.X × D.Zp
  shift : D.Zp
  targetPoint : D.X × D.Zp
  source_mem : ∃ omega : D.Omega, D.conclusion_relation_groupoid_reduction_zp_iota omega = sourcePoint
  target_mem : ∃ omega : D.Omega, D.conclusion_relation_groupoid_reduction_zp_iota omega = targetPoint
  action_eq : targetPoint = (sourcePoint.1, sourcePoint.2 + shift)

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_relation_id
    (D : conclusion_relation_groupoid_reduction_zp_data) (omega : D.Omega) :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D where
  source := omega
  target := omega
  same_base := rfl

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_relation_inv
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_relation_arrow D) :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D where
  source := a.target
  target := a.source
  same_base := a.same_base.symm

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_relation_comp
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a b : conclusion_relation_groupoid_reduction_zp_relation_arrow D)
    (h : a.target = b.source) :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D where
  source := a.source
  target := b.target
  same_base := by
    calc
      D.f a.source = D.f a.target := a.same_base
      _ = D.f b.source := congrArg D.f h
      _ = D.f b.target := b.same_base

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_relation_to_reduced
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_relation_arrow D) :
    conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D where
  sourcePoint := D.conclusion_relation_groupoid_reduction_zp_iota a.source
  shift := D.r a.target - D.r a.source
  targetPoint := D.conclusion_relation_groupoid_reduction_zp_iota a.target
  source_mem := ⟨a.source, rfl⟩
  target_mem := ⟨a.target, rfl⟩
  action_eq := by
    ext
    · exact a.same_base.symm
    · simp [conclusion_relation_groupoid_reduction_zp_iota]

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
noncomputable def conclusion_relation_groupoid_reduction_zp_reduced_source
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D) : D.Omega :=
  Classical.choose a.source_mem

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
noncomputable def conclusion_relation_groupoid_reduction_zp_reduced_target
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D) : D.Omega :=
  Classical.choose a.target_mem

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
noncomputable def conclusion_relation_groupoid_reduction_zp_reduced_to_relation
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D) :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D where
  source := D.conclusion_relation_groupoid_reduction_zp_reduced_source a
  target := D.conclusion_relation_groupoid_reduction_zp_reduced_target a
  same_base := by
    classical
    let omega := D.conclusion_relation_groupoid_reduction_zp_reduced_source a
    let omega' := D.conclusion_relation_groupoid_reduction_zp_reduced_target a
    have hsource :
        D.conclusion_relation_groupoid_reduction_zp_iota omega = a.sourcePoint :=
      Classical.choose_spec a.source_mem
    have htarget :
        D.conclusion_relation_groupoid_reduction_zp_iota omega' = a.targetPoint :=
      Classical.choose_spec a.target_mem
    have htarget_action :
        D.conclusion_relation_groupoid_reduction_zp_iota omega' =
          (a.sourcePoint.1, a.sourcePoint.2 + a.shift) := htarget.trans a.action_eq
    have hsource_base : D.f omega = a.sourcePoint.1 := by
      simpa [conclusion_relation_groupoid_reduction_zp_iota] using congrArg Prod.fst hsource
    have htarget_base : D.f omega' = a.sourcePoint.1 := by
      simpa [conclusion_relation_groupoid_reduction_zp_iota] using
        congrArg Prod.fst htarget_action
    exact hsource_base.trans htarget_base.symm

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_reduced_id
    (D : conclusion_relation_groupoid_reduction_zp_data) (omega : D.Omega) :
    conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D where
  sourcePoint := D.conclusion_relation_groupoid_reduction_zp_iota omega
  shift := 0
  targetPoint := D.conclusion_relation_groupoid_reduction_zp_iota omega
  source_mem := ⟨omega, rfl⟩
  target_mem := ⟨omega, rfl⟩
  action_eq := by
    ext <;> simp [conclusion_relation_groupoid_reduction_zp_iota]

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_reduced_inv
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a : conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D) :
    conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D where
  sourcePoint := a.targetPoint
  shift := -a.shift
  targetPoint := a.sourcePoint
  source_mem := a.target_mem
  target_mem := a.source_mem
  action_eq := by
    ext
    · exact (congrArg Prod.fst a.action_eq).symm
    · have hcoord := congrArg Prod.snd a.action_eq
      calc
        a.sourcePoint.2 = (a.sourcePoint.2 + a.shift) + -a.shift := by abel
        _ = a.targetPoint.2 + -a.shift := by rw [hcoord]

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def conclusion_relation_groupoid_reduction_zp_reduced_comp
    (D : conclusion_relation_groupoid_reduction_zp_data)
    (a b : conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D)
    (h : a.targetPoint = b.sourcePoint) :
    conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D where
  sourcePoint := a.sourcePoint
  shift := a.shift + b.shift
  targetPoint := b.targetPoint
  source_mem := a.source_mem
  target_mem := b.target_mem
  action_eq := by
    ext
    · have hb : b.targetPoint.1 = b.sourcePoint.1 := by rw [b.action_eq]
      have hba : b.sourcePoint.1 = a.targetPoint.1 := by rw [← h]
      have ha : a.targetPoint.1 = a.sourcePoint.1 := by rw [a.action_eq]
      exact hb.trans (hba.trans ha)
    · have hb : b.targetPoint.2 = b.sourcePoint.2 + b.shift := by rw [b.action_eq]
      have hba : b.sourcePoint.2 = a.targetPoint.2 := by rw [← h]
      have ha : a.targetPoint.2 = a.sourcePoint.2 + a.shift := by rw [a.action_eq]
      calc
        b.targetPoint.2 = b.sourcePoint.2 + b.shift := hb
        _ = a.targetPoint.2 + b.shift := by rw [hba]
        _ = (a.sourcePoint.2 + a.shift) + b.shift := by rw [ha]
        _ = a.sourcePoint.2 + (a.shift + b.shift) := by abel

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
structure conclusion_relation_groupoid_reduction_zp_iso
    (D : conclusion_relation_groupoid_reduction_zp_data) where
  toEquiv :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D ≃
      conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D
  source_preserving : ∀ a,
    (toEquiv a).sourcePoint =
      D.conclusion_relation_groupoid_reduction_zp_iota a.source
  target_preserving : ∀ a,
    (toEquiv a).targetPoint =
      D.conclusion_relation_groupoid_reduction_zp_iota a.target
  identity_preserving : ∀ omega,
    toEquiv (D.conclusion_relation_groupoid_reduction_zp_relation_id omega) =
      D.conclusion_relation_groupoid_reduction_zp_reduced_id omega
  inverse_preserving : ∀ a,
    toEquiv (D.conclusion_relation_groupoid_reduction_zp_relation_inv a) =
      D.conclusion_relation_groupoid_reduction_zp_reduced_inv (toEquiv a)
  composition_preserving : ∀ a b h,
    toEquiv (D.conclusion_relation_groupoid_reduction_zp_relation_comp a b h) =
      D.conclusion_relation_groupoid_reduction_zp_reduced_comp (toEquiv a) (toEquiv b) (by
        rw [target_preserving, source_preserving, h])

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
def relationGroupoidIsoReducedActionGroupoid
    (D : conclusion_relation_groupoid_reduction_zp_data) : Prop :=
  Nonempty (conclusion_relation_groupoid_reduction_zp_iso D)

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
noncomputable def conclusion_relation_groupoid_reduction_zp_relation_equiv_reduced
    (D : conclusion_relation_groupoid_reduction_zp_data) :
    conclusion_relation_groupoid_reduction_zp_relation_arrow D ≃
      conclusion_relation_groupoid_reduction_zp_reduced_action_arrow D where
  toFun := D.conclusion_relation_groupoid_reduction_zp_relation_to_reduced
  invFun := D.conclusion_relation_groupoid_reduction_zp_reduced_to_relation
  left_inv := by
    intro a
    ext
    · apply D.iota_injective
      exact Classical.choose_spec
        (D.conclusion_relation_groupoid_reduction_zp_relation_to_reduced a).source_mem
    · apply D.iota_injective
      exact Classical.choose_spec
        (D.conclusion_relation_groupoid_reduction_zp_relation_to_reduced a).target_mem
  right_inv := by
    intro a
    classical
    let omega := D.conclusion_relation_groupoid_reduction_zp_reduced_source a
    let omega' := D.conclusion_relation_groupoid_reduction_zp_reduced_target a
    have hsource :
        D.conclusion_relation_groupoid_reduction_zp_iota omega = a.sourcePoint :=
      Classical.choose_spec a.source_mem
    have htarget :
        D.conclusion_relation_groupoid_reduction_zp_iota omega' = a.targetPoint :=
      Classical.choose_spec a.target_mem
    have htarget_action :
        D.conclusion_relation_groupoid_reduction_zp_iota omega' =
          (a.sourcePoint.1, a.sourcePoint.2 + a.shift) := htarget.trans a.action_eq
    ext
    · simpa using congrArg Prod.fst hsource
    · simpa using congrArg Prod.snd hsource
    · have hsource_r : D.r omega = a.sourcePoint.2 := by
        simpa [conclusion_relation_groupoid_reduction_zp_iota] using congrArg Prod.snd hsource
      have htarget_r : D.r omega' = a.sourcePoint.2 + a.shift := by
        simpa [conclusion_relation_groupoid_reduction_zp_iota] using
          congrArg Prod.snd htarget_action
      calc
        D.r omega' - D.r omega = (a.sourcePoint.2 + a.shift) - a.sourcePoint.2 := by
          rw [htarget_r, hsource_r]
        _ = a.shift := by abel
    · simpa using congrArg Prod.fst htarget
    · simpa using congrArg Prod.snd htarget

/-- Paper label: `prop:conclusion-relation-groupoid-reduction-zp`. -/
theorem paper_conclusion_relation_groupoid_reduction_zp
    (D : conclusion_relation_groupoid_reduction_zp_data) :
    D.relationGroupoidIsoReducedActionGroupoid := by
  classical
  refine ⟨?_⟩
  refine
    { toEquiv := D.conclusion_relation_groupoid_reduction_zp_relation_equiv_reduced
      source_preserving := ?_
      target_preserving := ?_
      identity_preserving := ?_
      inverse_preserving := ?_
      composition_preserving := ?_ }
  · intro a
    rfl
  · intro a
    rfl
  · intro omega
    ext <;> simp [conclusion_relation_groupoid_reduction_zp_relation_equiv_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_to_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_id,
      conclusion_relation_groupoid_reduction_zp_reduced_id]
  · intro a
    ext <;> simp [conclusion_relation_groupoid_reduction_zp_relation_equiv_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_to_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_inv,
      conclusion_relation_groupoid_reduction_zp_reduced_inv]
  · intro a b h
    ext <;> simp [conclusion_relation_groupoid_reduction_zp_relation_equiv_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_to_reduced,
      conclusion_relation_groupoid_reduction_zp_relation_comp,
      conclusion_relation_groupoid_reduction_zp_reduced_comp, h]

end conclusion_relation_groupoid_reduction_zp_data

end Omega.Conclusion
