import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dcb-zg-density-riccati-euler`. The two scalar recurrences
imply the ratio Riccati equation, the one-step Euler factor for `u`, and the finite Euler product. -/
theorem paper_xi_time_part62dcb_zg_density_riccati_euler (p a b r u : ℕ → ℝ) (ha0 : a 0 = 1)
    (hb0 : b 0 = 0) (hr0 : r 0 = 0) (hu : ∀ i, u i = a i + b i)
    (hr : ∀ i ≥ 1, r i = b i / a i)
    (ha : ∀ i ≥ 1, a i = p i / (p i + 1) * (a (i - 1) + b (i - 1)))
    (hb : ∀ i ≥ 1, b i = (1 / (p i + 1)) * a (i - 1))
    (hpos : ∀ i, 1 ≤ i →
      a i ≠ 0 ∧ p i * (1 + r (i - 1)) ≠ 0 ∧
        (p i + 1) * (1 + r (i - 1)) ≠ 0) :
    (∀ i ≥ 1, r i = 1 / (p i * (1 + r (i - 1)))) ∧
      (∀ i ≥ 1,
        u i = u (i - 1) *
          (1 - r (i - 1) / ((p i + 1) * (1 + r (i - 1))))) ∧
      (∀ n,
        u n = (∏ i ∈ Finset.Icc 1 n,
          (1 - r (i - 1) / ((p i + 1) * (1 + r (i - 1)))))) := by
  let F : ℕ → ℝ :=
    fun i => 1 - r (i - 1) / ((p i + 1) * (1 + r (i - 1)))
  have hu0 : u 0 = 1 := by
    simp [hu, ha0, hb0]
  have hp_ne : ∀ i, 1 ≤ i → p i ≠ 0 := by
    intro i hi
    exact (mul_ne_zero_iff.mp (hpos i hi).2.1).1
  have hp1_ne : ∀ i, 1 ≤ i → p i + 1 ≠ 0 := by
    intro i hi
    exact (mul_ne_zero_iff.mp (hpos i hi).2.2).1
  have hone_ne : ∀ i, 1 ≤ i → 1 + r (i - 1) ≠ 0 := by
    intro i hi
    exact (mul_ne_zero_iff.mp (hpos i hi).2.2).2
  have ha_prev_ne : ∀ i, 1 ≤ i → a (i - 1) ≠ 0 := by
    intro i hi
    by_cases h1 : i = 1
    · subst i
      simp [ha0]
    · have hprev : 1 ≤ i - 1 := by omega
      exact (hpos (i - 1) hprev).1
  have hprev_ratio : ∀ i, 1 ≤ i → b (i - 1) = r (i - 1) * a (i - 1) := by
    intro i hi
    by_cases h1 : i = 1
    · subst i
      simp [hb0, hr0]
    · have hprev : 1 ≤ i - 1 := by omega
      have hane : a (i - 1) ≠ 0 := ha_prev_ne i hi
      rw [hr (i - 1) hprev]
      field_simp [hane]
  have hprev_sum : ∀ i, 1 ≤ i →
      a (i - 1) + b (i - 1) = a (i - 1) * (1 + r (i - 1)) := by
    intro i hi
    rw [hprev_ratio i hi]
    ring
  have hRiccati : ∀ i, 1 ≤ i → r i = 1 / (p i * (1 + r (i - 1))) := by
    intro i hi
    have hane : a (i - 1) ≠ 0 := ha_prev_ne i hi
    have hp : p i ≠ 0 := hp_ne i hi
    have hp1 : p i + 1 ≠ 0 := hp1_ne i hi
    have hone : 1 + r (i - 1) ≠ 0 := hone_ne i hi
    rw [hr i hi, hb i hi, ha i hi, hprev_sum i hi]
    field_simp [hane, hp, hp1, hone]
  have hEuler : ∀ i, 1 ≤ i → u i = u (i - 1) * F i := by
    intro i hi
    have hp1 : p i + 1 ≠ 0 := hp1_ne i hi
    have hone : 1 + r (i - 1) ≠ 0 := hone_ne i hi
    have hu_prev : u (i - 1) = a (i - 1) * (1 + r (i - 1)) := by
      rw [hu (i - 1), hprev_sum i hi]
    rw [hu i, ha i hi, hb i hi, hprev_sum i hi, hu_prev]
    dsimp [F]
    field_simp [hp1, hone]
    ring
  have hProduct : ∀ n, u n = ∏ i ∈ Finset.Icc 1 n, F i := by
    intro n
    induction n with
    | zero =>
        simp [hu0]
    | succ n ih =>
        rw [Finset.prod_Icc_succ_top (a := 1) (b := n) (by omega) F]
        rw [hEuler (n + 1) (by omega)]
        simp [ih]
  refine ⟨hRiccati, ?_, ?_⟩
  · intro i hi
    exact hEuler i hi
  · intro n
    simpa [F] using hProduct n

end Omega.Zeta
