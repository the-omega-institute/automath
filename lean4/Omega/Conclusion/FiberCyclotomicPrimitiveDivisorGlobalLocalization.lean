import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite fiber data for cyclotomic primitive-divisor localization. -/
structure conclusion_fiber_cyclotomic_primitive_divisor_global_localization_Data where
  X : Type
  instFintype : Fintype X
  instDecidableEq : DecidableEq X
  m : ℕ
  hm_pos : 0 < m
  cyclotomicIndex : ℕ
  tau : ℂ
  weight : X → ℕ
  Z : X → ℂ → ℂ
  primitiveMultiplicity : X → ℕ
  rowmotionOrder : X → ℕ
  global_weighted_partition :
    (Finset.univ : Finset X).sum (fun x => tau ^ weight x * Z x tau) = (1 + tau) ^ m
  positive_exponent_vanish :
    ∀ x, primitiveMultiplicity x ≠ 0 → Z x tau = 0
  multiplicity_zero_iff_rowmotion_no_three :
    ∀ x, primitiveMultiplicity x = 0 ↔ ¬ 3 ∣ rowmotionOrder x

/-- Paper-facing statement for global localization at a primitive cyclotomic root. -/
def conclusion_fiber_cyclotomic_primitive_divisor_global_localization_statement
    (D : conclusion_fiber_cyclotomic_primitive_divisor_global_localization_Data) : Prop :=
  letI := D.instFintype
  letI := D.instDecidableEq
  ((Finset.univ.filter (fun x : D.X => D.primitiveMultiplicity x = 0)).sum
      (fun x => D.tau ^ D.weight x * D.Z x D.tau) =
    (1 + D.tau) ^ D.m) ∧
  (D.cyclotomicIndex = 3 →
    D.tau = -1 →
      (Finset.univ.filter (fun x : D.X => ¬ 3 ∣ D.rowmotionOrder x)).sum
        (fun x => (-1 : ℂ) ^ D.weight x * D.Z x (-1)) = 0)

/-- Paper label:
`thm:conclusion-fiber-cyclotomic-primitive-divisor-global-localization`. -/
theorem paper_conclusion_fiber_cyclotomic_primitive_divisor_global_localization
    (D : conclusion_fiber_cyclotomic_primitive_divisor_global_localization_Data) :
    conclusion_fiber_cyclotomic_primitive_divisor_global_localization_statement D := by
  letI := D.instFintype
  letI := D.instDecidableEq
  have hlocalized :
      (Finset.univ.filter (fun x : D.X => D.primitiveMultiplicity x = 0)).sum
          (fun x => D.tau ^ D.weight x * D.Z x D.tau) =
        (1 + D.tau) ^ D.m := by
    have hpositive_zero :
        (Finset.univ.filter (fun x : D.X => ¬ D.primitiveMultiplicity x = 0)).sum
            (fun x => D.tau ^ D.weight x * D.Z x D.tau) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxpos : D.primitiveMultiplicity x ≠ 0 := by
        simpa using (Finset.mem_filter.mp hx).2
      simp [D.positive_exponent_vanish x hxpos]
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset D.X))
        (p := fun x : D.X => D.primitiveMultiplicity x = 0)
        (f := fun x => D.tau ^ D.weight x * D.Z x D.tau)
    calc
      (Finset.univ.filter (fun x : D.X => D.primitiveMultiplicity x = 0)).sum
          (fun x => D.tau ^ D.weight x * D.Z x D.tau)
          =
        (Finset.univ : Finset D.X).sum
          (fun x => D.tau ^ D.weight x * D.Z x D.tau) := by
            rw [← hsplit, hpositive_zero, add_zero]
      _ = (1 + D.tau) ^ D.m := D.global_weighted_partition
  refine ⟨hlocalized, ?_⟩
  intro _hD htau
  have hpow_zero : (1 + D.tau) ^ D.m = 0 := by
    rw [htau]
    norm_num [Nat.ne_of_gt D.hm_pos]
  calc
    (Finset.univ.filter (fun x : D.X => ¬ 3 ∣ D.rowmotionOrder x)).sum
        (fun x => (-1 : ℂ) ^ D.weight x * D.Z x (-1))
        =
      (Finset.univ.filter (fun x : D.X => D.primitiveMultiplicity x = 0)).sum
        (fun x => D.tau ^ D.weight x * D.Z x D.tau) := by
          refine Finset.sum_congr ?_ ?_
          · ext x
            simp [D.multiplicity_zero_iff_rowmotion_no_three x]
          · intro x _hx
            rw [htau]
    _ = (1 + D.tau) ^ D.m := hlocalized
    _ = 0 := hpow_zero

end Omega.Conclusion
