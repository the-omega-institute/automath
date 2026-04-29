import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xabWindow6LocalFourierMultipliersExactZeroSet

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xab-window6-hidden-averaging-alias-hyperplanes`.
The global hidden-averaging zero locus is the union of the audited coordinate alias
hyperplanes; the three-point local branch has empty zero set. -/
theorem paper_xi_time_part9xab_window6_hidden_averaging_alias_hyperplanes
    {Lambda : Type*} [Fintype Lambda] (d : Lambda -> Fin 3) :
    forall t : Lambda -> xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue,
      (exists x,
        (d x = 0 ∧
            xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero
              (t x)) ∨
          (d x = 1 ∧
            xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero
              (t x)) ∨
          (d x = 2 ∧
            xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero
              (t x))) ↔
        (exists x,
          (d x = 0 ∧
            t x ∈
              ({⟨16, by omega⟩, ⟨48, by omega⟩} :
                Finset
                  xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue)) ∨
            (d x = 2 ∧
              t x ∈
                ({⟨16, by omega⟩, ⟨32, by omega⟩, ⟨48, by omega⟩} :
                  Finset
                    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue))) := by
  rcases paper_xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set with
    ⟨hm2Set, hm3Set, hm4Set⟩
  have hm2 :
      ∀ r : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue,
        xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero r ↔
          r ∈
            ({⟨16, by omega⟩, ⟨48, by omega⟩} :
              Finset xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) := by
    intro r
    constructor
    · intro hr
      have hmem :
          r ∈
            Finset.univ.filter
              xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
      simpa [hm2Set] using hmem
    · intro hr
      have hmem :
          r ∈
            Finset.univ.filter
              xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero := by
        simpa [hm2Set] using hr
      exact (Finset.mem_filter.mp hmem).2
  have hm3 :
      ∀ r : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue,
        ¬ xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero r := by
    intro r hr
    have hmem :
        r ∈
          Finset.univ.filter
            xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
    simp [hm3Set] at hmem
  have hm4 :
      ∀ r : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue,
        xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero r ↔
          r ∈
            ({⟨16, by omega⟩, ⟨32, by omega⟩, ⟨48, by omega⟩} :
              Finset xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) := by
    intro r
    constructor
    · intro hr
      have hmem :
          r ∈
            Finset.univ.filter
              xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
      simpa [hm4Set] using hmem
    · intro hr
      have hmem :
          r ∈
            Finset.univ.filter
              xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero := by
        simpa [hm4Set] using hr
      exact (Finset.mem_filter.mp hmem).2
  intro t
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rcases hx with hx2 | hx3 | hx4
    · exact Or.inl ⟨hx2.1, (hm2 (t x)).mp hx2.2⟩
    · exact False.elim (hm3 (t x) hx3.2)
    · exact Or.inr ⟨hx4.1, (hm4 (t x)).mp hx4.2⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rcases hx with hx2 | hx4
    · exact Or.inl ⟨hx2.1, (hm2 (t x)).mpr hx2.2⟩
    · exact Or.inr (Or.inr ⟨hx4.1, (hm4 (t x)).mpr hx4.2⟩)

end Omega.Zeta
