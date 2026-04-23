import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6HalfblockRecoversLucasDivisorLattice

namespace Omega.DerivedConsequences

open scoped BigOperators

noncomputable section

/-- Concrete data for the halfblock Lucas/Ramanujan factorization package. -/
structure derived_window6_halfblock_lucas_ramanujan_factorization_data where
  factorizationData : derived_window6_halfblock_recovers_lucas_divisor_lattice_data
  q : ℕ
  ramanujanHalfShadow : ℤ

/-- The halfblock level `d`. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_level
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : ℕ :=
  derived_window6_halfblock_recovers_lucas_divisor_lattice_level D.factorizationData

/-- The Lucas half-factor `L_d`. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : ℕ :=
  Omega.lucasNum (derived_window6_halfblock_lucas_ramanujan_factorization_level D)

/-- The Fibonacci half-factor `F_d`. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_fibFactor
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : ℤ :=
  Nat.fib (derived_window6_halfblock_lucas_ramanujan_factorization_level D)

/-- The symbolic Ramanujan sum `Σ_d(q)`. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_sigma
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : ℤ :=
  if D.q ∣ derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor D then
    derived_window6_halfblock_lucas_ramanujan_factorization_fibFactor D * D.ramanujanHalfShadow
  else
    0

/-- The normalized Ramanujan shadow `Σ_d(q) / F_{2d}`. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_normalizedSigma
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : ℚ :=
  (derived_window6_halfblock_lucas_ramanujan_factorization_sigma D : ℚ) /
    Nat.fib (2 * derived_window6_halfblock_lucas_ramanujan_factorization_level D)

/-- Paper-facing Lucas/Ramanujan factorization package for the halfblock witness. -/
def derived_window6_halfblock_lucas_ramanujan_factorization_statement
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) : Prop :=
  derived_window6_halfblock_recovers_lucas_divisor_lattice_statement D.factorizationData ∧
    derived_window6_halfblock_lucas_ramanujan_factorization_sigma D =
      (if D.q ∣ derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor D then
        derived_window6_halfblock_lucas_ramanujan_factorization_fibFactor D *
          D.ramanujanHalfShadow
      else
        0) ∧
    derived_window6_halfblock_lucas_ramanujan_factorization_normalizedSigma D =
      (if D.q ∣ derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor D then
        (D.ramanujanHalfShadow : ℚ) /
          derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor D
      else
        0)

theorem derived_window6_halfblock_lucas_ramanujan_factorization_fib_double_cast
    (d : ℕ) (hd : 1 ≤ d) :
    (Nat.fib (2 * d) : ℚ) = (Nat.fib d : ℚ) * Omega.lucasNum d := by
  have hnat :
      Nat.fib (2 * d) = Nat.fib d * Omega.lucasNum d := by
    calc
      Nat.fib (2 * d) = Nat.fib d * (Nat.fib (2 * d) / Nat.fib d) := by
        exact (Nat.mul_div_cancel' (Omega.Zeta.fib_dvd_fib_double d)).symm
      _ = Nat.fib d * Omega.lucasNum d := by
        rw [Omega.Zeta.fib_double_div_eq_lucas d hd]
  exact_mod_cast hnat

/-- Paper label: `thm:derived-window6-halfblock-lucas-ramanujan-factorization`. -/
theorem paper_derived_window6_halfblock_lucas_ramanujan_factorization
    (D : derived_window6_halfblock_lucas_ramanujan_factorization_data) :
    derived_window6_halfblock_lucas_ramanujan_factorization_statement D := by
  have hFactor :=
    paper_derived_window6_halfblock_recovers_lucas_divisor_lattice D.factorizationData
  let d := derived_window6_halfblock_lucas_ramanujan_factorization_level D
  have hd : 1 ≤ d := by
    dsimp [d, derived_window6_halfblock_lucas_ramanujan_factorization_level,
      derived_window6_halfblock_recovers_lucas_divisor_lattice_level]
    omega
  refine ⟨hFactor, rfl, ?_⟩
  by_cases hdiv : D.q ∣ derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor D
  · have hfib_ne : (Nat.fib d : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.fib_pos.mpr hd).ne'
    have hlucas_pos : 0 < Omega.lucasNum d := by
      rw [Omega.lucasNum_eq_fib d hd]
      have hfib_pos : 0 < Nat.fib (d + 1) := Nat.fib_pos.mpr (by omega)
      omega
    have hlucas_ne : (Omega.lucasNum d : ℚ) ≠ 0 := by
      exact_mod_cast hlucas_pos.ne'
    have hcalc :
        (((((Nat.fib d : ℤ) * D.ramanujanHalfShadow : ℤ) : ℚ)) / (Nat.fib (2 * d) : ℚ)) =
          (D.ramanujanHalfShadow : ℚ) / Omega.lucasNum d := by
      push_cast
      rw [derived_window6_halfblock_lucas_ramanujan_factorization_fib_double_cast d hd]
      field_simp [hfib_ne, hlucas_ne]
    dsimp [d] at hcalc ⊢
    have hcond : D.q ∣ Omega.lucasNum
        (derived_window6_halfblock_lucas_ramanujan_factorization_level D) := by
      simpa [derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor] using hdiv
    unfold derived_window6_halfblock_lucas_ramanujan_factorization_normalizedSigma
      derived_window6_halfblock_lucas_ramanujan_factorization_sigma
      derived_window6_halfblock_lucas_ramanujan_factorization_fibFactor
      derived_window6_halfblock_lucas_ramanujan_factorization_lucasFactor
    rw [if_pos hcond, if_pos hcond]
    exact hcalc
  · unfold derived_window6_halfblock_lucas_ramanujan_factorization_normalizedSigma
      derived_window6_halfblock_lucas_ramanujan_factorization_sigma
    simp [hdiv]

end

end Omega.DerivedConsequences
