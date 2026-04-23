import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Functions on the ambient sample space `Ω`. -/
abbrev conclusion_fiber_intermediate_system_operator_mobius_correction_function_space
    (Ω : Type*) := Ω → ℝ

/-- Endomorphisms of the function space, viewed as the concrete conditional-expectation operators. -/
abbrev conclusion_fiber_intermediate_system_operator_mobius_correction_operator
    (Ω : Type*) :=
  Module.End ℝ
    (conclusion_fiber_intermediate_system_operator_mobius_correction_function_space Ω)

/-- The Möbius-primitive operator attached to an intermediate factorization `g`. -/
def conclusion_fiber_intermediate_system_operator_mobius_correction_primitive
    {ι Ω : Type*} [DecidableEq ι] [Fintype ι]
    (E : Finset ι →
      conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω)
    (g : Finset ι) :
    conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω :=
  ∑ h ∈ Finset.Iic g,
    IncidenceAlgebra.mu
        (conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω) h g *
      E h

private lemma conclusion_fiber_intermediate_system_operator_mobius_correction_reconstruct
    {ι Ω : Type*} [DecidableEq ι] [Fintype ι]
    (E : Finset ι →
      conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω)
    (g : Finset ι) :
    (∑ h ∈ Finset.Iic g,
        conclusion_fiber_intermediate_system_operator_mobius_correction_primitive E h) =
      E g := by
  classical
  let R := conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω
  calc
    ∑ h ∈ Finset.Iic g,
        conclusion_fiber_intermediate_system_operator_mobius_correction_primitive E h =
      ∑ h ∈ Finset.Iic g, ∑ k ∈ Finset.Iic h, IncidenceAlgebra.mu R k h * E k := by
        rfl
    _ = ∑ k ∈ Finset.Iic g, ∑ h ∈ Finset.Icc k g, IncidenceAlgebra.mu R k h * E k := by
        rw [Finset.sum_sigma' (Finset.Iic g) fun h => Finset.Iic h]
        rw [Finset.sum_sigma' (Finset.Iic g) fun k => Finset.Icc k g]
        apply Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩)
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_Iic, Finset.mem_Icc] at hx ⊢
          exact ⟨hx.2.trans hx.1, hx.2, hx.1⟩
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_Iic, Finset.mem_Icc] at hx ⊢
          exact ⟨hx.2.2, hx.2.1⟩
        · intro x hx
          simp
        · intro x hx
          simp
        · intro x hx
          simp
    _ = ∑ k ∈ Finset.Iic g, (∑ h ∈ Finset.Icc k g, IncidenceAlgebra.mu R k h) * E k := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [← Finset.sum_mul]
    _ = ∑ k ∈ Finset.Iic g, (if k = g then 1 else 0) * E k := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [IncidenceAlgebra.sum_Icc_mu_right]
    _ = E g := by
        rw [Finset.sum_eq_single g]
        · simp
        · intro k hk hkg
          simp [hkg]
        · intro hg
          exact (hg (by simp)).elim

/-- Paper label: `thm:conclusion-fiber-intermediate-system-operator-mobius-correction`. On the
finite intermediate-system lattice `Finset ι`, every operator family admits a unique Möbius
primitive family, and the top-layer truncation splits into the exact complementary remainder. -/
theorem paper_conclusion_fiber_intermediate_system_operator_mobius_correction
    {ι Ω : Type*} [DecidableEq ι] [Fintype ι]
    (E : Finset ι →
      conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω) :
    let D :=
      conclusion_fiber_intermediate_system_operator_mobius_correction_primitive E;
    (∀ g, E g = ∑ h ∈ Finset.Iic g, D h) ∧
      (∀ D' :
          Finset ι →
            conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω,
        (∀ g, E g = ∑ h ∈ Finset.Iic g, D' h) → D' = D) ∧
      E (Finset.univ : Finset ι) = ∑ g ∈ Finset.Iic (Finset.univ : Finset ι), D g ∧
      ∀ g0 : Finset ι,
        E (Finset.univ : Finset ι) - E g0 =
          ∑ g ∈ (Finset.Iic (Finset.univ : Finset ι)).filter (fun g => ¬ g ⊆ g0), D g := by
  classical
  let D :=
    conclusion_fiber_intermediate_system_operator_mobius_correction_primitive E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    simpa [D] using
      (conclusion_fiber_intermediate_system_operator_mobius_correction_reconstruct E g).symm
  · intro D' hD'
    funext g
    calc
      D' g =
        ∑ h ∈ Finset.Iic g,
          IncidenceAlgebra.mu
              (conclusion_fiber_intermediate_system_operator_mobius_correction_operator Ω) h g *
            E h := by
              exact IncidenceAlgebra.moebius_inversion_bot D' E hD' g
      _ = D g := by
            rfl
  · simpa [D] using
      (conclusion_fiber_intermediate_system_operator_mobius_correction_reconstruct E
        (Finset.univ : Finset ι)).symm
  · intro g0
    have htop :
        E (Finset.univ : Finset ι) = ∑ g ∈ Finset.Iic (Finset.univ : Finset ι), D g := by
      simpa [D] using
        (conclusion_fiber_intermediate_system_operator_mobius_correction_reconstruct E
          (Finset.univ : Finset ι)).symm
    have hg0 : E g0 = ∑ g ∈ Finset.Iic g0, D g := by
      simpa [D] using
        (conclusion_fiber_intermediate_system_operator_mobius_correction_reconstruct E g0).symm
    have hfilter :
        (Finset.Iic (Finset.univ : Finset ι)).filter (fun g : Finset ι => g ⊆ g0) =
          Finset.Iic g0 := by
      ext g
      simp
    calc
      E (Finset.univ : Finset ι) - E g0 =
        (∑ g ∈ Finset.Iic (Finset.univ : Finset ι), D g) - ∑ g ∈ Finset.Iic g0, D g := by
          rw [htop, hg0]
      _ =
        (∑ g ∈ (Finset.Iic (Finset.univ : Finset ι)).filter (fun g : Finset ι => g ⊆ g0), D g) +
          ∑ g ∈
              (Finset.Iic (Finset.univ : Finset ι)).filter (fun g : Finset ι => ¬ g ⊆ g0), D g -
            ∑ g ∈ Finset.Iic g0, D g := by
              rw [← Finset.sum_filter_add_sum_filter_not
                (s := Finset.Iic (Finset.univ : Finset ι))
                (p := fun g : Finset ι => g ⊆ g0) (f := D)]
      _ =
        (∑ g ∈ Finset.Iic g0, D g) +
          ∑ g ∈
              (Finset.Iic (Finset.univ : Finset ι)).filter (fun g : Finset ι => ¬ g ⊆ g0), D g -
            ∑ g ∈ Finset.Iic g0, D g := by
              rw [hfilter]
      _ =
        ∑ g ∈
            (Finset.Iic (Finset.univ : Finset ι)).filter (fun g : Finset ι => ¬ g ⊆ g0), D g := by
          abel

end Omega.Conclusion
