import Mathlib.Tactic
import Omega.Zeta.XiTimePart51AADerivedCrossFibGcdFormula
import Omega.Zeta.XiTimePart51AADoublingLucasExtension

namespace Omega.Zeta

/-- The concrete two-window seed corresponding to the pair `(6, 14)`. -/
def xi_time_part51aa_window14_strict_direct_factor_lift_data :
    XiDerivedCrossFibGcdFormulaData where
  windows := [6, 14]

/-- The `window-6` modulus in the Fibonacci model. -/
def xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus : Nat :=
  Nat.fib (6 + 2)

/-- The doubled `window-14` modulus in the Fibonacci model. -/
def xi_time_part51aa_window14_strict_direct_factor_lift_window14_modulus : Nat :=
  Nat.fib (14 + 2)

/-- Concrete package for the `window-14` strict direct-factor lift over `window-6`. -/
def xi_time_part51aa_window14_strict_direct_factor_lift_spec : Prop :=
  xi_time_part51aa_doubling_lucas_extension_spec 7 ∧
    xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus = 21 ∧
    xi_time_part51aa_window14_strict_direct_factor_lift_window14_modulus = 987 ∧
    Omega.lucasNum 8 = 47 ∧
    xi_time_part51aa_window14_strict_direct_factor_lift_window14_modulus =
      xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus * 47 ∧
    Nat.Coprime xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus 47 ∧
    let D := xi_time_part51aa_window14_strict_direct_factor_lift_data
    D.modulusGcd = xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus ∧
      D.homologyMultiplicity 0 = 1 ∧
      D.homologyMultiplicity 1 = 1 ∧
      D.homologyMultiplicity 2 = 0

/-- Paper label: `cor:xi-time-part51aa-window14-strict-direct-factor-lift`. The doubled
Lucas-extension package at shifted index `8` identifies the new direct factor `47`, while the
derived-cross Fibonacci gcd formula on the window pair `(6,14)` shows that the shared derived
core remains the `21`-point window-`6` modulus with homology multiplicities concentrated in
degrees `0` and `1`. -/
theorem paper_xi_time_part51aa_window14_strict_direct_factor_lift :
    xi_time_part51aa_window14_strict_direct_factor_lift_spec := by
  have hdouble_package := paper_xi_time_part51aa_doubling_lucas_extension 7
  let D := xi_time_part51aa_window14_strict_direct_factor_lift_data
  have hderived := paper_xi_time_part51aa_derived_cross_fib_gcd_formula D
  have hcollapse : D.modulusGcd = Nat.fib (Nat.gcd (6 + 2) (14 + 2)) := by
    simpa [D, xi_time_part51aa_window14_strict_direct_factor_lift_data,
      XiDerivedCrossFibGcdFormulaData.fibGcdCollapse, XiDerivedCrossFibGcdFormulaData.modulusGcd,
      XiDerivedCrossFibGcdFormulaData.indexGcd, XiDerivedCrossFibGcdFormulaData.moduli,
      XiDerivedCrossFibGcdFormulaData.shiftedWindows, fibWindowModulus] using hderived.2.1
  have hhomology0 : D.homologyMultiplicity 0 = 1 := by
    simpa [D, xi_time_part51aa_window14_strict_direct_factor_lift_data,
      XiDerivedCrossFibGcdFormulaData.homologyMultiplicity]
      using hderived.2.2 0
  have hhomology1 : D.homologyMultiplicity 1 = 1 := by
    simpa [D, xi_time_part51aa_window14_strict_direct_factor_lift_data,
      XiDerivedCrossFibGcdFormulaData.homologyMultiplicity]
      using hderived.2.2 1
  have hhomology2 : D.homologyMultiplicity 2 = 0 := by
    simpa [D, xi_time_part51aa_window14_strict_direct_factor_lift_data,
      XiDerivedCrossFibGcdFormulaData.homologyMultiplicity]
      using hderived.2.2 2
  rcases hdouble_package with ⟨hprod, hquot, hgcd_bridge, hgcd_exact, hcoprime⟩
  refine ⟨⟨hprod, hquot, hgcd_bridge, hgcd_exact, hcoprime⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus, Nat.fib]
  · norm_num [xi_time_part51aa_window14_strict_direct_factor_lift_window14_modulus, Nat.fib]
  · norm_num [Omega.lucasNum]
  · norm_num [xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus,
      xi_time_part51aa_window14_strict_direct_factor_lift_window14_modulus, Nat.fib]
  · simpa [xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus, Nat.fib] using
      hcoprime
  · refine ⟨?_, hhomology0, hhomology1, hhomology2⟩
    calc
      D.modulusGcd = Nat.fib (Nat.gcd (6 + 2) (14 + 2)) := hcollapse
      _ = Nat.fib 8 := by norm_num
      _ = xi_time_part51aa_window14_strict_direct_factor_lift_window6_modulus := by
        rfl

end Omega.Zeta
