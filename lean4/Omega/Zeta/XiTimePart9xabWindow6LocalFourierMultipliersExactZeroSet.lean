import Mathlib.Tactic

namespace Omega.Zeta

/-- Residues modulo `64` for the window-`6` local Fourier multipliers. -/
abbrev xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue := Fin 64

/-- Multiplication of a residue by an integer exponent, reduced modulo `64`. -/
def xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue
    (a : ℕ) (t : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) :
    ℕ :=
  (a * t.val) % 64

/-- Zero predicate for `m_2(t) = (1 + omega^(34t)) / 2`. -/
def xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero
    (t : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) : Prop :=
  xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 34 t = 32

instance xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_decidable_m2_zero :
    DecidablePred
      xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero := by
  intro t
  unfold xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero
  infer_instance

/-- Exponent-arithmetic certificate for a three-term root-of-unity cancellation. -/
def xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero
    (t : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) : Prop :=
  (3 * xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 21 t) %
        64 = 0 ∧
    (3 * xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 34 t) %
        64 = 0 ∧
    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 21 t ≠ 0 ∧
    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 34 t ≠ 0 ∧
    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 21 t ≠
      xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 34 t

instance xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_decidable_m3_zero :
    DecidablePred
      xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero := by
  intro t
  unfold xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero
  infer_instance

/-- Zero predicate for `m_4(t) = ((1 + omega^(21t)) (1 + omega^(34t))) / 4`. -/
def xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero
    (t : xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue) : Prop :=
  xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 21 t = 32 ∨
    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_mulResidue 34 t = 32

instance xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_decidable_m4_zero :
    DecidablePred
      xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero := by
  intro t
  unfold xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero
  infer_instance

/-- The exact zero-set statement for the three window-`6` local Fourier multipliers. -/
def xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_statement : Prop :=
  (Finset.univ.filter
      xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m2_zero =
    ({⟨16, by omega⟩, ⟨48, by omega⟩} :
      Finset xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue)) ∧
    (Finset.univ.filter
        xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m3_zero =
      (∅ : Finset xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue)) ∧
    (Finset.univ.filter
        xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_m4_zero =
      ({⟨16, by omega⟩, ⟨32, by omega⟩, ⟨48, by omega⟩} :
        Finset xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_residue))

/-- Paper label:
`thm:xi-time-part9xab-window6-local-fourier-multipliers-exact-zero-set`. -/
theorem paper_xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set :
    xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_statement := by
  unfold xi_time_part9xab_window6_local_fourier_multipliers_exact_zero_set_statement
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext t
    fin_cases t <;> native_decide

end Omega.Zeta
