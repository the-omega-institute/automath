import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The collapsed Möbius-log contribution of the `(1 - z)` branch. -/
def mobius_collapse_one_minus (z : ℂ) : ℂ :=
  -Complex.log (1 - z)

/-- The collapsed Möbius-log contribution of the `(1 + z)` branch. -/
def mobius_collapse_one_plus (z : ℂ) : ℂ :=
  Complex.log (1 + z)

/-- Paper label: `lem:mobius-collapse`. Inside the open unit disk, both `1 - z` and `1 + z` have
positive real part, so the logarithm of their product splits without crossing the branch cut; the
`(1 + z)` term can therefore be rewritten as the difference of the two `(1 - z)` logarithms. -/
theorem paper_mobius_collapse (z : ℂ) (hz : ‖z‖ < 1) :
    mobius_collapse_one_minus z = -Complex.log (1 - z) ∧
      mobius_collapse_one_plus z = Complex.log (1 - z ^ 2) - Complex.log (1 - z) := by
  have hzre : |z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
  rcases abs_lt.mp hzre with ⟨hzre_lower, hzre_upper⟩
  have hre_sub : 0 < (1 - z).re := by
    simpa [Complex.sub_re] using sub_pos.mpr hzre_upper
  have hre_add : 0 < (1 + z).re := by
    have : 0 < 1 + z.re := by linarith
    simpa [Complex.add_re] using this
  have hne_sub : 1 - z ≠ 0 := by
    intro h
    have : (1 - z).re = 0 := by simpa [h]
    linarith
  have hne_add : 1 + z ≠ 0 := by
    intro h
    have : (1 + z).re = 0 := by simpa [h]
    linarith
  have harg_sub : |Complex.arg (1 - z)| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff (z := 1 - z)).2 (Or.inl hre_sub)
  have harg_add : |Complex.arg (1 + z)| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff (z := 1 + z)).2 (Or.inl hre_add)
  rcases abs_lt.mp harg_sub with ⟨harg_sub_lower, harg_sub_upper⟩
  rcases abs_lt.mp harg_add with ⟨harg_add_lower, harg_add_upper⟩
  have harg_sum :
      Complex.arg (1 - z) + Complex.arg (1 + z) ∈ Set.Ioc (-Real.pi) Real.pi := by
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  have hlog_mul :
      Complex.log ((1 - z) * (1 + z)) = Complex.log (1 - z) + Complex.log (1 + z) :=
    Complex.log_mul hne_sub hne_add harg_sum
  have hfactor : (1 - z) * (1 + z) = 1 - z ^ 2 := by
    ring
  refine ⟨rfl, ?_⟩
  have hsum : Complex.log (1 - z ^ 2) = Complex.log (1 - z) + Complex.log (1 + z) := by
    simpa [hfactor] using hlog_mul
  calc
    mobius_collapse_one_plus z = Complex.log (1 + z) := by rfl
    _ = (Complex.log (1 - z) + Complex.log (1 + z)) - Complex.log (1 - z) := by abel
    _ = Complex.log (1 - z ^ 2) - Complex.log (1 - z) := by rw [hsum]

end

end Omega.SyncKernelRealInput
