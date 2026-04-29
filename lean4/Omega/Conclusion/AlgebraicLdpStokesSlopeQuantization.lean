import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-algebraic-ldp-stokes-slope-quantization`. -/
theorem paper_conclusion_algebraic_ldp_stokes_slope_quantization (S : Set ℤ) (h0 : (0 : ℤ) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (hneg : ∀ a ∈ S, -a ∈ S) :
    ∃! m : ℕ, S = {z : ℤ | (m : ℤ) ∣ z} := by
  let H : AddSubgroup ℤ := {
    carrier := S
    zero_mem' := h0
    add_mem' := fun ha hb => hadd _ ha _ hb
    neg_mem' := fun ha => hneg _ ha
  }
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp inferInstance
  refine ⟨g.natAbs, ?_, ?_⟩
  · ext z
    calc
      z ∈ S ↔ z ∈ H := Iff.rfl
      _ ↔ z ∈ AddSubgroup.zmultiples g := by rw [hg]
      _ ↔ z ∈ AddSubgroup.zmultiples (g.natAbs : ℤ) := by rw [Int.zmultiples_natAbs]
      _ ↔ (g.natAbs : ℤ) ∣ z := Int.mem_zmultiples_iff
  · intro n hn
    have hg_dvd_n : (g.natAbs : ℤ) ∣ (n : ℤ) := by
      have : (n : ℤ) ∈ S := by
        rw [hn]
        exact dvd_refl (n : ℤ)
      rw [show S = H by rfl, ← hg, ← Int.zmultiples_natAbs] at this
      exact Int.mem_zmultiples_iff.mp this
    have hn_dvd_g : (n : ℤ) ∣ (g.natAbs : ℤ) := by
      have : (g.natAbs : ℤ) ∈ S := by
        rw [show S = H by rfl, ← hg, ← Int.zmultiples_natAbs]
        exact Int.mem_zmultiples_iff.mpr (dvd_refl (g.natAbs : ℤ))
      simpa [hn] using this
    exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hn_dvd_g)
      (Int.natCast_dvd_natCast.mp hg_dvd_n)

end Omega.Conclusion
