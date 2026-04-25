import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiWindow6B3C3TightFrameFourthMomentNonsimilarity

namespace Omega.Zeta

/-- Concrete window-`6` weight/dictionary data on the `18` cyclic states. Equality of the
filtered weight-one set with the short-root and long-root filters is the finite dictionary input
read off from the paper tables. -/
structure XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData where
  weight : Fin 18 → ℕ
  b3Root : Fin 18 → XiWindow6Root
  c3Root : Fin 18 → XiWindow6Root
  weight_le_three : ∀ w : Fin 18, weight w ≤ 3
  b3WeightOneStates :
    (Finset.univ.filter fun w : Fin 18 => weight w = 1) =
      Finset.univ.filter fun w : Fin 18 => b3Root w ∈ xiWindow6B3ShortRoots.toFinset
  c3WeightOneStates :
    (Finset.univ.filter fun w : Fin 18 => weight w = 1) =
      Finset.univ.filter fun w : Fin 18 => c3Root w ∈ xiWindow6LongRoots.toFinset

namespace XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData

/-- In the `B₃` dictionary, weight `1` is exactly the short-root orbit. -/
def b3_weight_one_iff_short_root
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) : Prop :=
  ∀ w : Fin 18, D.weight w = 1 ↔ D.b3Root w ∈ xiWindow6B3ShortRoots.toFinset

/-- In the `C₃` dictionary, weight `1` is exactly the long-root orbit. -/
def c3_weight_one_iff_long_root
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) : Prop :=
  ∀ w : Fin 18, D.weight w = 1 ↔ D.c3Root w ∈ xiWindow6LongRoots.toFinset

/-- Both Weyl orbit splittings are controlled by the same Hamming-weight partition. -/
def weyl_orbits_determined_by_weight
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) : Prop :=
  ∀ u v : Fin 18, D.weight u = D.weight v →
    ((D.b3Root u ∈ xiWindow6B3ShortRoots.toFinset ↔
        D.b3Root v ∈ xiWindow6B3ShortRoots.toFinset) ∧
      (D.c3Root u ∈ xiWindow6LongRoots.toFinset ↔
        D.c3Root v ∈ xiWindow6LongRoots.toFinset))

/-- The weight-one indicator is the cubic Lagrange interpolant on the values `0, 1, 2, 3`. -/
def weight_one_indicator_is_cubic
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) : Prop :=
  ∀ w : Fin 18,
    (if D.weight w = 1 then (1 : ℚ) else 0) =
      ((D.weight w : ℚ) * ((D.weight w : ℚ) - 2) * ((D.weight w : ℚ) - 3)) / 2

end XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData

open XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData

private lemma paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) (w : Fin 18) :
    D.weight w = 1 ↔ D.b3Root w ∈ xiWindow6B3ShortRoots.toFinset := by
  have hmem := congrArg (fun s : Finset (Fin 18) => w ∈ s) D.b3WeightOneStates
  simpa using hmem

private lemma paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) (w : Fin 18) :
    D.weight w = 1 ↔ D.c3Root w ∈ xiWindow6LongRoots.toFinset := by
  have hmem := congrArg (fun s : Finset (Fin 18) => w ∈ s) D.c3WeightOneStates
  simpa using hmem

/-- Paper label: `thm:xi-time-part62dea-window6-weight-determines-weyl-orbits`. Equality of the
weight-one slice with the short-root `B₃` orbit and the long-root `C₃` orbit implies that both
Weyl splittings are controlled by Hamming weight, and the weight-one indicator is the cubic
Lagrange interpolant on the admissible weights `0, 1, 2, 3`. -/
theorem paper_xi_time_part62dea_window6_weight_determines_weyl_orbits
    (D : XiTimePart62deaWindow6WeightDeterminesWeylOrbitsData) :
    D.b3_weight_one_iff_short_root ∧ D.c3_weight_one_iff_long_root ∧
      D.weyl_orbits_determined_by_weight ∧ D.weight_one_indicator_is_cubic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    exact paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem D w
  · intro w
    exact paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem D w
  · intro u v huv
    refine ⟨?_, ?_⟩
    · constructor
      · intro hu
        have hu1 :
            D.weight u = 1 :=
          (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem D u).mpr hu
        have hv1 : D.weight v = 1 := by simpa [huv] using hu1
        exact (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem D v).mp hv1
      · intro hv
        have hv1 :
            D.weight v = 1 :=
          (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem D v).mpr hv
        have hu1 : D.weight u = 1 := by simpa [huv] using hv1
        exact (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_b3_mem D u).mp hu1
    · constructor
      · intro hu
        have hu1 :
            D.weight u = 1 :=
          (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem D u).mpr hu
        have hv1 : D.weight v = 1 := by simpa [huv] using hu1
        exact (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem D v).mp hv1
      · intro hv
        have hv1 :
            D.weight v = 1 :=
          (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem D v).mpr hv
        have hu1 : D.weight u = 1 := by simpa [huv] using hv1
        exact (paper_xi_time_part62dea_window6_weight_determines_weyl_orbits_c3_mem D u).mp hu1
  · intro w
    have hw : D.weight w ≤ 3 := D.weight_le_three w
    interval_cases h : D.weight w <;> norm_num [h]

end Omega.Zeta
