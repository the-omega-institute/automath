import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_size_two_fibers := Fin 8

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_size_three_fibers := Fin 4

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_size_four_fibers := Fin 9

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_visible_modes := Fin 21

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_mass_two_modes := Fin 8

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_mass_three_modes := Fin 8

abbrev conclusion_window6_fiber_gauge_laplacian_spectrum_mass_four_modes := Fin 27

/-- The complete-graph fiber Laplacian `d I - J` on a fiber of size `d`. -/
def conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian
    (d : ℕ) (v : Fin d → ℚ) : Fin d → ℚ :=
  fun i => (d : ℚ) * v i - ∑ j : Fin d, v j

/-- Constant vectors on one finite fiber. -/
def conclusion_window6_fiber_gauge_laplacian_spectrum_constant
    (d : ℕ) (c : ℚ) : Fin d → ℚ :=
  fun _ => c

/-- Zero-sum vectors on one finite fiber. -/
def conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum
    (d : ℕ) (v : Fin d → ℚ) : Prop :=
  ∑ i : Fin d, v i = 0

def conclusion_window6_fiber_gauge_laplacian_spectrum_statement : Prop :=
  (∀ (d : ℕ) (c : ℚ),
      conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian d
        (conclusion_window6_fiber_gauge_laplacian_spectrum_constant d c) = 0) ∧
    (∀ (d : ℕ) (v : Fin d → ℚ),
      conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum d v →
        conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian d v =
          fun i => (d : ℚ) * v i) ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_visible_modes = 21 ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_two_modes =
      Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_size_two_fibers *
        (2 - 1) ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_three_modes =
      Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_size_three_fibers *
        (3 - 1) ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_four_modes =
      Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_size_four_fibers *
        (4 - 1) ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_two_modes = 8 ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_three_modes = 8 ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_mass_four_modes = 27

lemma conclusion_window6_fiber_gauge_laplacian_spectrum_constant_kernel
    (d : ℕ) (c : ℚ) :
    conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian d
      (conclusion_window6_fiber_gauge_laplacian_spectrum_constant d c) = 0 := by
  funext i
  simp [conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian,
    conclusion_window6_fiber_gauge_laplacian_spectrum_constant]

lemma conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum_eigen
    (d : ℕ) (v : Fin d → ℚ)
    (hv : conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum d v) :
    conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian d v =
      fun i => (d : ℚ) * v i := by
  funext i
  rw [conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum] at hv
  simp [conclusion_window6_fiber_gauge_laplacian_spectrum_laplacian, hv]

/-- Paper label: `thm:conclusion-window6-fiber-gauge-laplacian-spectrum`. -/
theorem paper_conclusion_window6_fiber_gauge_laplacian_spectrum :
    conclusion_window6_fiber_gauge_laplacian_spectrum_statement := by
  refine ⟨conclusion_window6_fiber_gauge_laplacian_spectrum_constant_kernel,
    conclusion_window6_fiber_gauge_laplacian_spectrum_zero_sum_eigen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_visible_modes]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_two_modes,
      conclusion_window6_fiber_gauge_laplacian_spectrum_size_two_fibers]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_three_modes,
      conclusion_window6_fiber_gauge_laplacian_spectrum_size_three_fibers]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_four_modes,
      conclusion_window6_fiber_gauge_laplacian_spectrum_size_four_fibers]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_two_modes]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_three_modes]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_mass_four_modes]

end

end Omega.Conclusion
