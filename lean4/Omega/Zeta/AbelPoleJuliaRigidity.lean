import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The damped Abel pole radius written using only the real part of the pole. -/
def xi_abel_pole_julia_rigidity_radius (b reRho δ : ℝ) : ℝ :=
  Real.exp (-(reRho - (1 / 2 + δ)) * Real.log b)

/-- The `k`-th iterate of the power map `r ↦ r^m`, written in closed form. -/
def xi_abel_pole_julia_rigidity_iterate (m k : ℕ) (r : ℝ) : ℝ :=
  r ^ (m ^ k)

/-- The Julia set for the real power map is the unit circle in modulus. -/
def xi_abel_pole_julia_rigidity_julia_set (_m : ℕ) : Set ℝ :=
  {r | |r| = 1}

/-- Paper label: `thm:xi-abel-pole-julia-rigidity`.
For the damped Abel pole radius, the half-line test on `Re ρ` is equivalent to the modulus test,
and the real power iterates split into the three standard Julia regimes. -/
theorem paper_xi_abel_pole_julia_rigidity (m : ℕ) (b : ℝ) (δ : ℝ) :
    2 ≤ m → 1 < b →
      ∀ reRho : ℝ,
        let r := xi_abel_pole_julia_rigidity_radius b reRho δ
        (reRho > 1 / 2 + δ ↔ |r| < 1) ∧
          (reRho < 1 / 2 + δ ↔ 1 < |r|) ∧
          (reRho = 1 / 2 + δ ↔ r ∈ xi_abel_pole_julia_rigidity_julia_set m) ∧
          (|r| < 1 →
            ∀ k : ℕ,
              |xi_abel_pole_julia_rigidity_iterate m k r| = |r| ^ (m ^ k) ∧
                |xi_abel_pole_julia_rigidity_iterate m k r| < 1) ∧
          (|r| = 1 →
            ∀ k : ℕ, |xi_abel_pole_julia_rigidity_iterate m k r| = 1) ∧
          (1 < |r| →
            ∀ k : ℕ, 1 < |xi_abel_pole_julia_rigidity_iterate m k r|) := by
  intro hm hb reRho
  dsimp
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hr_pos : 0 < xi_abel_pole_julia_rigidity_radius b reRho δ := by
    unfold xi_abel_pole_julia_rigidity_radius
    exact Real.exp_pos _
  have hr_abs :
      |xi_abel_pole_julia_rigidity_radius b reRho δ| =
        Real.exp (-(reRho - (1 / 2 + δ)) * Real.log b) := by
    rw [abs_of_pos hr_pos]
    rfl
  have hm_ne_zero : m ≠ 0 := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr_abs, Real.exp_lt_one_iff]
    constructor
    · intro hre
      have hneg : -(reRho - (1 / 2 + δ)) < 0 := by linarith
      have := mul_lt_mul_of_pos_right hneg hlogb
      simpa using this
    · intro hlt
      have hneg : -(reRho - (1 / 2 + δ)) < 0 := by
        have : -(reRho - (1 / 2 + δ)) * Real.log b < 0 * Real.log b := by
          simpa using hlt
        exact lt_of_mul_lt_mul_right this hlogb.le
      linarith
  · rw [hr_abs, Real.one_lt_exp_iff]
    constructor
    · intro hre
      have hpos : 0 < -(reRho - (1 / 2 + δ)) := by linarith
      have := mul_lt_mul_of_pos_right hpos hlogb
      simpa [mul_comm] using this
    · intro hgt
      have hpos : 0 < -(reRho - (1 / 2 + δ)) := by
        have : 0 * Real.log b < -(reRho - (1 / 2 + δ)) * Real.log b := by
          simpa [mul_comm] using hgt
        exact lt_of_mul_lt_mul_right this hlogb.le
      linarith
  · constructor
    · intro hre
      rw [xi_abel_pole_julia_rigidity_julia_set, Set.mem_setOf_eq, hr_abs, Real.exp_eq_one_iff]
      simp [hre]
    · intro hr
      rw [xi_abel_pole_julia_rigidity_julia_set, Set.mem_setOf_eq, hr_abs, Real.exp_eq_one_iff]
        at hr
      have hzero : -(reRho - (1 / 2 + δ)) = 0 := by
        exact (mul_eq_zero.mp hr).resolve_right hlogb.ne'
      have hdiff : reRho - (1 / 2 + δ) = 0 := by
        linarith
      linarith
  · intro hr_lt k
    have hmk_ne_zero : m ^ k ≠ 0 := pow_ne_zero _ hm_ne_zero
    refine ⟨by simp [xi_abel_pole_julia_rigidity_iterate, abs_pow], ?_⟩
    simpa [xi_abel_pole_julia_rigidity_iterate, abs_pow] using
      (pow_lt_one₀ (abs_nonneg _) hr_lt hmk_ne_zero)
  · intro hr_eq k
    simp [xi_abel_pole_julia_rigidity_iterate, abs_pow, hr_eq]
  · intro hr_gt k
    have hmk_ne_zero : m ^ k ≠ 0 := pow_ne_zero _ hm_ne_zero
    simpa [xi_abel_pole_julia_rigidity_iterate, abs_pow] using
      (one_lt_pow₀ hr_gt hmk_ne_zero)

end

end Omega.Zeta
