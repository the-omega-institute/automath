import Omega.Folding.InverseLimitTopology

namespace Omega.RecursiveAddressing.InverseLimitDeterminacy

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a compatible inverse-limit family determines a unique stable address, and
    stable addresses are exactly determined by their finite prefixes.
    thm:inverse-limit-determinacy -/
theorem paper_scan_projection_address_inverse_limit_determinacy_seeds :
    (∀ F : Omega.X.CompatibleFamily, ∃! a : Omega.X.XInfinity, Omega.X.toFamily a = F) ∧
    (∀ a b : Omega.X.XInfinity, (∀ m, Omega.X.prefixWord a m = Omega.X.prefixWord b m) ↔ a = b) ∧
    Function.Bijective (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) := by
  refine ⟨?_, ?_, Omega.X.CompatibleFamily_complete⟩
  · intro F
    refine ⟨Omega.X.ofFamily F, Omega.X.toFamily_ofFamily F, ?_⟩
    intro a ha
    have := congrArg Omega.X.ofFamily ha
    simpa using this
  · intro a b
    exact (Omega.X.XInfinity_eq_iff a b).symm

/-- Wrapper theorem matching the ETDS publication label.
    thm:inverse-limit-determinacy -/
theorem paper_scan_projection_address_inverse_limit_determinacy_package :
    (∀ F : Omega.X.CompatibleFamily, ∃! a : Omega.X.XInfinity, Omega.X.toFamily a = F) ∧
    (∀ a b : Omega.X.XInfinity, (∀ m, Omega.X.prefixWord a m = Omega.X.prefixWord b m) ↔ a = b) ∧
    Function.Bijective (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) :=
  paper_scan_projection_address_inverse_limit_determinacy_seeds

private theorem eq_of_dist_le_dyadic
    {Y : Type} [MetricSpace Y] {C : ℝ} {x y : Y}
    (_hC : 0 ≤ C)
    (hbound : ∀ n : Nat, dist x y ≤ C / (2 : ℝ) ^ n) : x = y := by
  apply eq_of_dist_eq_zero
  have hpow :
      Filter.Tendsto (fun n : Nat => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) := by
    have hhalf_nonneg : 0 ≤ (1 : ℝ) / 2 := by norm_num
    have hhalf_lt_one : (1 : ℝ) / 2 < 1 := by norm_num
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hhalf_nonneg hhalf_lt_one
  have hgeom :
      Filter.Tendsto (fun n : Nat => C / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hpow.const_mul C
  have hdist0 : Filter.Tendsto (fun _ : Nat => dist x y) Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => dist_nonneg) hbound hgeom
  exact tendsto_nhds_unique tendsto_const_nhds hdist0

set_option maxHeartbeats 400000 in
/-- Publication wrapper for
    `thm:recursive-addressing-dyadic-inverse-limit-stable-object`.
    It packages the inverse-limit determinacy equivalence, the basic topology of
    `XInfinity`, and the shrinking-diameter uniqueness principle for the associated
    stable point object. -/
theorem paper_recursive_addressing_dyadic_inverse_limit_stable_object :
    (∀ F : Omega.X.CompatibleFamily, ∃! a : Omega.X.XInfinity, Omega.X.toFamily a = F) ∧
    (∀ a b : Omega.X.XInfinity, (∀ m, Omega.X.prefixWord a m = Omega.X.prefixWord b m) ↔ a = b) ∧
    Function.Bijective (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) ∧
    Nonempty Omega.X.XInfinity ∧
    IsCompact (Set.univ : Set Omega.X.XInfinity) ∧
    (∀ a b : Omega.X.XInfinity, a = b ↔ ∀ n, a.1 n = b.1 n) ∧
    (∀ a b : Omega.X.XInfinity, ∀ n, a.1 n ≠ b.1 n → a ≠ b) ∧
    (∀ {Y : Type} [MetricSpace Y] {C : ℝ} {x y : Y},
      0 ≤ C →
      (∀ n : Nat, dist x y ≤ C / (2 : ℝ) ^ n) →
      x = y) := by
  rcases paper_scan_projection_address_inverse_limit_determinacy_package with ⟨huniq, hprefix, hbij⟩
  rcases Omega.X.paper_XInfinity_topology_package with ⟨hnonempty, hcompact, hbits, hne⟩
  refine ⟨huniq, ?_, hbij, hnonempty, hcompact, hbits, hne, ?_⟩
  · intro a b
    exact hprefix a b
  · intro Y _ C x y hC hbound
    exact eq_of_dist_le_dyadic hC hbound

end Omega.RecursiveAddressing.InverseLimitDeterminacy
