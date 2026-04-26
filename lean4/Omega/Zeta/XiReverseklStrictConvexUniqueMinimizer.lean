import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiReverseKLAffineSecondVariationStrongConvex
import Omega.Zeta.XiReverseKLCyclicEnergyEquivalence

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Affine chord between two coefficient vectors. -/
def xi_reversekl_strict_convex_unique_minimizer_mix {n : ℕ} (t : ℝ)
    (c₀ c₁ : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => (1 - t) * c₀ k + t * c₁ k

/-- Quadratic energy of a finite Fourier profile. -/
def xi_reversekl_strict_convex_unique_minimizer_profile_energy {n : ℕ}
    (u : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, (u k) ^ 2

/-- Reverse-KL seed energy after Poisson smoothing. -/
def xi_reversekl_strict_convex_unique_minimizer_energy {n : ℕ} (r : ℝ)
    (c : Fin (n + 1) → ℝ) : ℝ :=
  xi_reversekl_strict_convex_unique_minimizer_profile_energy (xiPoissonSmoothedProfile r c)

/-- Squared Poisson-smoothed difference energy. -/
def xi_reversekl_strict_convex_unique_minimizer_smoothed_gap_energy {n : ℕ} (r : ℝ)
    (c₀ c₁ : Fin (n + 1) → ℝ) : ℝ :=
  xi_reversekl_strict_convex_unique_minimizer_profile_energy
    (fun k => xiPoissonSmoothedProfile r c₁ k - xiPoissonSmoothedProfile r c₀ k)

/-- Concrete convexity for subsets of finite Fourier coefficient vectors. -/
def xi_reversekl_strict_convex_unique_minimizer_convex {n : ℕ}
    (C : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ ⦃c₀ c₁⦄, c₀ ∈ C → c₁ ∈ C → ∀ t, 0 ≤ t → t ≤ 1 →
    xi_reversekl_strict_convex_unique_minimizer_mix t c₀ c₁ ∈ C

/-- Minimizers on a concrete constraint set. -/
def xi_reversekl_strict_convex_unique_minimizer_is_minimizer {n : ℕ} (r : ℝ)
    (C : Set (Fin (n + 1) → ℝ)) (c : Fin (n + 1) → ℝ) : Prop :=
  c ∈ C ∧
    ∀ d, d ∈ C →
      xi_reversekl_strict_convex_unique_minimizer_energy r c ≤
        xi_reversekl_strict_convex_unique_minimizer_energy r d

/-- Uniqueness means any two minimizers on the convex set coincide. -/
def xi_reversekl_strict_convex_unique_minimizer_unique_minimizer {n : ℕ} (r : ℝ)
    (C : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ ⦃c₀ c₁⦄,
    xi_reversekl_strict_convex_unique_minimizer_is_minimizer r C c₀ →
      xi_reversekl_strict_convex_unique_minimizer_is_minimizer r C c₁ →
        c₀ = c₁

/-- Exact quadratic chord-gap identity for the finite-dimensional seed energy. -/
def xi_reversekl_strict_convex_unique_minimizer_second_variation {n : ℕ} (r : ℝ) : Prop :=
  ∀ (c₀ c₁ : Fin (n + 1) → ℝ) (t : ℝ),
    (1 - t) * xi_reversekl_strict_convex_unique_minimizer_energy r c₀ +
        t * xi_reversekl_strict_convex_unique_minimizer_energy r c₁ -
        xi_reversekl_strict_convex_unique_minimizer_energy r
          (xi_reversekl_strict_convex_unique_minimizer_mix t c₀ c₁) =
      t * (1 - t) *
        xi_reversekl_strict_convex_unique_minimizer_smoothed_gap_energy r c₀ c₁

/-- Strict convexity on every affine chord. -/
def xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap {n : ℕ}
    (r : ℝ) : Prop :=
  ∀ (c₀ c₁ : Fin (n + 1) → ℝ) (t : ℝ),
    c₀ ≠ c₁ →
      0 < t →
        t < 1 →
          xi_reversekl_strict_convex_unique_minimizer_energy r
              (xi_reversekl_strict_convex_unique_minimizer_mix t c₀ c₁) <
            (1 - t) * xi_reversekl_strict_convex_unique_minimizer_energy r c₀ +
              t * xi_reversekl_strict_convex_unique_minimizer_energy r c₁

lemma xi_reversekl_strict_convex_unique_minimizer_smoothed_profile_mix {n : ℕ} (r t : ℝ)
    (c₀ c₁ : Fin (n + 1) → ℝ) :
    xiPoissonSmoothedProfile r
        (xi_reversekl_strict_convex_unique_minimizer_mix t c₀ c₁) =
      xi_reversekl_strict_convex_unique_minimizer_mix t
        (xiPoissonSmoothedProfile r c₀) (xiPoissonSmoothedProfile r c₁) := by
  funext k
  simp [xi_reversekl_strict_convex_unique_minimizer_mix, xiPoissonSmoothedProfile]
  ring

lemma xi_reversekl_strict_convex_unique_minimizer_poisson_smoothed_injective {n : ℕ}
    {r : ℝ} (hr : 0 < r) :
    Function.Injective (fun c : Fin (n + 1) → ℝ => xiPoissonSmoothedProfile r c) := by
  intro c₀ c₁ h
  funext k
  have hk := congrFun h k
  dsimp [xiPoissonSmoothedProfile] at hk
  exact mul_left_cancel₀ (pow_ne_zero _ (ne_of_gt hr)) hk

lemma xi_reversekl_strict_convex_unique_minimizer_exists_differing_coordinate {n : ℕ}
    {u₀ u₁ : Fin (n + 1) → ℝ} (h : u₀ ≠ u₁) : ∃ k, u₀ k ≠ u₁ k := by
  by_contra h'
  apply h
  funext k
  by_contra hk
  exact h' ⟨k, hk⟩

lemma xi_reversekl_strict_convex_unique_minimizer_profile_energy_pos_of_ne {n : ℕ}
    {u₀ u₁ : Fin (n + 1) → ℝ} (h : u₀ ≠ u₁) :
    0 < xi_reversekl_strict_convex_unique_minimizer_profile_energy (fun k => u₁ k - u₀ k) := by
  obtain ⟨k, hk⟩ := xi_reversekl_strict_convex_unique_minimizer_exists_differing_coordinate h
  have hterm_pos : 0 < (u₁ k - u₀ k) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hk.symm)
  have hterm_le :
      (u₁ k - u₀ k) ^ 2 ≤
        ∑ i : Fin (n + 1), (u₁ i - u₀ i) ^ 2 := by
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun i : Fin (n + 1) => (u₁ i - u₀ i) ^ 2)
        (by
          intro i hi
          positivity)
        (Finset.mem_univ k))
  exact lt_of_lt_of_le hterm_pos hterm_le

lemma xi_reversekl_strict_convex_unique_minimizer_profile_energy_second_variation {n : ℕ}
    (u₀ u₁ : Fin (n + 1) → ℝ) (t : ℝ) :
    (1 - t) * xi_reversekl_strict_convex_unique_minimizer_profile_energy u₀ +
        t * xi_reversekl_strict_convex_unique_minimizer_profile_energy u₁ -
        xi_reversekl_strict_convex_unique_minimizer_profile_energy
          (xi_reversekl_strict_convex_unique_minimizer_mix t u₀ u₁) =
      t * (1 - t) *
        xi_reversekl_strict_convex_unique_minimizer_profile_energy (fun k => u₁ k - u₀ k) := by
  calc
    (1 - t) * xi_reversekl_strict_convex_unique_minimizer_profile_energy u₀ +
        t * xi_reversekl_strict_convex_unique_minimizer_profile_energy u₁ -
        xi_reversekl_strict_convex_unique_minimizer_profile_energy
          (xi_reversekl_strict_convex_unique_minimizer_mix t u₀ u₁) =
      (∑ k, (1 - t) * (u₀ k) ^ 2) +
        (∑ k, t * (u₁ k) ^ 2) -
        ∑ k, (xi_reversekl_strict_convex_unique_minimizer_mix t u₀ u₁ k) ^ 2 := by
          simp [xi_reversekl_strict_convex_unique_minimizer_profile_energy, Finset.mul_sum]
    _ = ∑ k,
        ((1 - t) * (u₀ k) ^ 2 + t * (u₁ k) ^ 2 -
          (xi_reversekl_strict_convex_unique_minimizer_mix t u₀ u₁ k) ^ 2) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ k, t * (1 - t) * (u₁ k - u₀ k) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [xi_reversekl_strict_convex_unique_minimizer_mix]
          ring
    _ = t * (1 - t) *
        xi_reversekl_strict_convex_unique_minimizer_profile_energy (fun k => u₁ k - u₀ k) := by
          simp [xi_reversekl_strict_convex_unique_minimizer_profile_energy, Finset.mul_sum, mul_assoc]

lemma xi_reversekl_strict_convex_unique_minimizer_second_variation_true {n : ℕ} (r : ℝ) :
    xi_reversekl_strict_convex_unique_minimizer_second_variation (n := n) r := by
  unfold xi_reversekl_strict_convex_unique_minimizer_second_variation
  intro c₀ c₁ t
  unfold xi_reversekl_strict_convex_unique_minimizer_energy
    xi_reversekl_strict_convex_unique_minimizer_smoothed_gap_energy
  rw [xi_reversekl_strict_convex_unique_minimizer_smoothed_profile_mix]
  exact xi_reversekl_strict_convex_unique_minimizer_profile_energy_second_variation
    (xiPoissonSmoothedProfile r c₀) (xiPoissonSmoothedProfile r c₁) t

lemma xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap_true {n : ℕ}
    {r : ℝ} (hr : 0 < r ∧ r < 1) :
    xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap (n := n) r := by
  unfold xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap
  intro c₀ c₁ t hneq ht₀ ht₁
  have hsmoothed_ne :
      xiPoissonSmoothedProfile r c₀ ≠ xiPoissonSmoothedProfile r c₁ := by
    intro h
    exact hneq
      (xi_reversekl_strict_convex_unique_minimizer_poisson_smoothed_injective
        (n := n) hr.1 h)
  have hgap_pos :
      0 <
        t * (1 - t) *
          xi_reversekl_strict_convex_unique_minimizer_profile_energy
            (fun k =>
              xiPoissonSmoothedProfile r c₁ k - xiPoissonSmoothedProfile r c₀ k) := by
    have hcoeff : 0 < t * (1 - t) := by
      nlinarith
    have henergy :
        0 <
          xi_reversekl_strict_convex_unique_minimizer_profile_energy
            (fun k => xiPoissonSmoothedProfile r c₁ k - xiPoissonSmoothedProfile r c₀ k) :=
      xi_reversekl_strict_convex_unique_minimizer_profile_energy_pos_of_ne hsmoothed_ne
    exact mul_pos hcoeff henergy
  have hsecond :=
    xi_reversekl_strict_convex_unique_minimizer_second_variation_true (n := n) r c₀ c₁ t
  have :
      0 <
        (1 - t) * xi_reversekl_strict_convex_unique_minimizer_energy r c₀ +
          t * xi_reversekl_strict_convex_unique_minimizer_energy r c₁ -
          xi_reversekl_strict_convex_unique_minimizer_energy r
            (xi_reversekl_strict_convex_unique_minimizer_mix t c₀ c₁) := by
    rw [hsecond]
    exact hgap_pos
  linarith

lemma xi_reversekl_strict_convex_unique_minimizer_unique_of_convex {n : ℕ} {r : ℝ}
    {C : Set (Fin (n + 1) → ℝ)} (hr : 0 < r ∧ r < 1)
    (hC : xi_reversekl_strict_convex_unique_minimizer_convex C) :
    xi_reversekl_strict_convex_unique_minimizer_unique_minimizer r C := by
  intro c₀ c₁ hc₀ hc₁
  by_contra hneq
  have hmid :
      xi_reversekl_strict_convex_unique_minimizer_mix (1 / 2 : ℝ) c₀ c₁ ∈ C :=
    hC hc₀.1 hc₁.1 (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hstrict :=
    (xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap_true
      (n := n) hr c₀ c₁ (1 / 2 : ℝ) hneq (by norm_num) (by norm_num)
      )
  have hc₀_le :
      xi_reversekl_strict_convex_unique_minimizer_energy r c₀ ≤
        xi_reversekl_strict_convex_unique_minimizer_energy r
          (xi_reversekl_strict_convex_unique_minimizer_mix (1 / 2 : ℝ) c₀ c₁) :=
    hc₀.2 _ hmid
  have hc₁_le :
      xi_reversekl_strict_convex_unique_minimizer_energy r c₁ ≤
        xi_reversekl_strict_convex_unique_minimizer_energy r
          (xi_reversekl_strict_convex_unique_minimizer_mix (1 / 2 : ℝ) c₀ c₁) :=
    hc₁.2 _ hmid
  have havg_le :
      (1 - (1 / 2 : ℝ)) * xi_reversekl_strict_convex_unique_minimizer_energy r c₀ +
          (1 / 2 : ℝ) * xi_reversekl_strict_convex_unique_minimizer_energy r c₁ ≤
        xi_reversekl_strict_convex_unique_minimizer_energy r
          (xi_reversekl_strict_convex_unique_minimizer_mix (1 / 2 : ℝ) c₀ c₁) := by
    nlinarith
  linarith

/-- Paper label: `cor:xi-reversekl-strict-convex-unique-minimizer`. The finite-dimensional
Poisson-smoothed quadratic reverse-KL seed is strictly convex on every affine chord, hence admits
at most one minimizer on any convex constraint set. -/
theorem paper_xi_reversekl_strict_convex_unique_minimizer :
    ∀ (n : ℕ) (r : ℝ) (C : Set (Fin (n + 1) → ℝ)),
      (0 < r ∧ r < 1) →
        xi_reversekl_strict_convex_unique_minimizer_convex C →
          xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap (n := n) r ∧
            xi_reversekl_strict_convex_unique_minimizer_unique_minimizer r C := by
  intro n r C hr hC
  have hsecond :
      xi_reversekl_strict_convex_unique_minimizer_second_variation (n := n) r :=
    xi_reversekl_strict_convex_unique_minimizer_second_variation_true (n := n) r
  have hgap :
      xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap (n := n) r :=
    xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap_true (n := n) hr
  have hpackage :=
    paper_xi_reversekl_affine_second_variation_strong_convex
      (xi_reversekl_strict_convex_unique_minimizer_second_variation (n := n) r)
      (xi_reversekl_strict_convex_unique_minimizer_strong_convex_chord_gap (n := n) r)
      hsecond hgap
  exact ⟨hpackage.2,
    xi_reversekl_strict_convex_unique_minimizer_unique_of_convex (n := n) hr hC⟩

end

end Omega.Zeta
