import Omega.Folding.BinGaugeVolume
import Omega.Folding.FiberEntropySaturation

namespace Omega.Folding

open scoped BigOperators

/-- The order-`2` collision moment of a finite fiber profile. -/
noncomputable def hypercube_gauge_volume_renyi_upperbound_collision_moment {α : Type*} [Fintype α]
    (d : α → ℕ) : ℝ :=
  ∑ a, (d a : ℝ) ^ 2

/-- Concrete order-`2` Rényi upper bound for the normalized gauge volume density of a hypercube
pushforward profile. -/
def hypercube_gauge_volume_renyi_upperbound_hypercube_gauge_volume_renyi_upperbound_statement :
    Prop :=
  ∀ {α : Type*} [Fintype α], ∀ (n : ℕ) (d : α → ℕ),
    (∀ a, 1 ≤ d a) →
      (∑ a, d a = 2 ^ n) →
        binGaugeG n d ≤
          Real.log
            (hypercube_gauge_volume_renyi_upperbound_collision_moment d / (2 : ℝ) ^ n)

local notation "hypercube_gauge_volume_renyi_upperbound_statement" =>
  hypercube_gauge_volume_renyi_upperbound_hypercube_gauge_volume_renyi_upperbound_statement

/-- Paper label: `prop:hypercube-gauge-volume-renyi-upperbound`. -/
theorem paper_hypercube_gauge_volume_renyi_upperbound :
    hypercube_gauge_volume_renyi_upperbound_statement := by
  intro α _ n d hd hsum
  have hbin :=
    (paper_fold_bin_gauge_volume (α := α) n d hd hsum).2
  have hpow_pos : 0 < (2 : ℝ) ^ n := by
    positivity
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := hpow_pos.ne'
  have hsumR : (∑ a, (d a : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast hsum
  let pi : α → ℝ := fun a => (d a : ℝ) / (2 : ℝ) ^ n
  have hpi_nonneg : ∀ a, 0 ≤ pi a := by
    intro a
    exact div_nonneg (by positivity) hpow_pos.le
  have hpi_sum : ∑ a, pi a = 1 := by
    unfold pi
    calc
      ∑ a, (d a : ℝ) / (2 : ℝ) ^ n = (∑ a, (d a : ℝ)) / (2 : ℝ) ^ n := by
        rw [Finset.sum_div]
      _ = (2 : ℝ) ^ n / (2 : ℝ) ^ n := by rw [hsumR]
      _ = 1 := by field_simp [hpow_ne]
  have hsat :=
    (paper_fold_fiber_entropy_saturation (pi := pi) (d := d) hpi_nonneg hpi_sum
      (fun a => Nat.succ_le_iff.mp (hd a))).1
  have hkappa_eq :
      binGaugeKappa n d = ∑ a, pi a * Real.log (d a : ℝ) := by
    unfold binGaugeKappa pi
    calc
      (∑ a, (d a : ℝ) * Real.log (d a)) / (2 : ℝ) ^ n =
          ∑ a, ((d a : ℝ) * Real.log (d a)) / (2 : ℝ) ^ n := by
            rw [Finset.sum_div]
      _ = ∑ a, ((d a : ℝ) / (2 : ℝ) ^ n) * Real.log (d a : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            field_simp [hpow_ne]
      _ = ∑ a, pi a * Real.log (d a : ℝ) := by rfl
  have hmoment_eq :
      ∑ a, pi a * (d a : ℝ) =
        hypercube_gauge_volume_renyi_upperbound_collision_moment d / (2 : ℝ) ^ n := by
    unfold pi hypercube_gauge_volume_renyi_upperbound_collision_moment
    calc
      ∑ a, ((d a : ℝ) / (2 : ℝ) ^ n) * (d a : ℝ) =
          ∑ a, ((d a : ℝ) ^ 2) / (2 : ℝ) ^ n := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            field_simp [hpow_ne]
      _ = (∑ a, (d a : ℝ) ^ 2) / (2 : ℝ) ^ n := by
            rw [← Finset.sum_div]
  calc
    binGaugeG n d ≤ binGaugeKappa n d := hbin
    _ = ∑ a, pi a * Real.log (d a : ℝ) := hkappa_eq
    _ ≤ Real.log (∑ a, pi a * (d a : ℝ)) := hsat
    _ = Real.log
          (hypercube_gauge_volume_renyi_upperbound_collision_moment d / (2 : ℝ) ^ n) := by
          rw [hmoment_eq]

end Omega.Folding
