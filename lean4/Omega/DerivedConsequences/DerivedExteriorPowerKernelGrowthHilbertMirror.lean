import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Tactic
import Omega.CircleDimension.FiniteProbeExtraction
import Omega.Zeta.XiExteriorPowerGaussianBinomHilbert

namespace Omega.DerivedConsequences

open scoped BigOperators
open Omega.Zeta

noncomputable section

/-- The `k`-subset family of `{0,1,…,q}`. -/
def paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family
    (q k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (q + 1)).powersetCard k

/-- The global involution extending `i ↦ q - i` on `{0,1,…,q}`. -/
def paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index
    (q i : ℕ) : ℕ :=
  if i ≤ q then q - i else i

/-- Mirror a `k`-subset across the staircase involution `i ↦ q - i`. -/
def paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset
    (q : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q)

/-- The truncated kernel-growth sum attached to the exterior-power Smith exponent multiset. -/
def paper_derived_exterior_power_kernel_growth_hilbert_mirror_kernel_growth
    (q k r : ℕ) : ℕ :=
  (((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.map
      fun S => min (Finset.sum S fun i => i) r).sum)

/-- The `s`-th Hilbert layer count, realized as the number of exponents strictly larger than `s`. -/
def paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer
    (q k s : ℕ) : ℕ :=
  ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter fun S =>
      s < Finset.sum S fun i => i).card

/-- Concrete statement packaging the multiset kernel-growth formula, the Hilbert-layer first
difference law, and the mirror complement identity. -/
def derived_exterior_power_kernel_growth_hilbert_mirror_statement (q k : ℕ) : Prop :=
  (∀ r,
      paper_derived_exterior_power_kernel_growth_hilbert_mirror_kernel_growth q k r =
        (((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.map
            fun S => min (Finset.sum S fun i => i) r).sum)) ∧
    (∀ s,
      paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k s =
        paper_derived_exterior_power_kernel_growth_hilbert_mirror_kernel_growth q k (s + 1) -
          paper_derived_exterior_power_kernel_growth_hilbert_mirror_kernel_growth q k s) ∧
    (∀ s, s < k * q →
      paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k s +
          paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k
            (k * q - 1 - s) =
        Nat.choose (q + 1) k)

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_injective
    (q : ℕ) :
    Function.Injective
      (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q) := by
  intro a b hab
  unfold paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index at hab
  by_cases ha : a ≤ q <;> by_cases hb : b ≤ q <;> simp [ha, hb] at hab ⊢ <;> omega

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_involutive
    {q i : ℕ} (hi : i ≤ q) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q
        (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q i) =
      i := by
  have hqi : q - i ≤ q := by omega
  simp [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index, hi, hqi]
  omega

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_mem_family
    {q k : ℕ} {S : Finset ℕ}
    (hS : S ∈ paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q S ∈
      paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k := by
  have hS' : S ∈ (Finset.range (q + 1)).powersetCard k := by
    simpa [paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family] using hS
  rw [Finset.mem_powersetCard] at hS'
  rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family, Finset.mem_powersetCard]
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS'.1 hi))
    simp [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index, hiq]
  · rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset]
    rw [Finset.card_image_of_injective _]
    · exact hS'.2
    · exact paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_injective q

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_involutive
    {q : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range (q + 1)) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q
        (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q S) =
      S := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
    rcases Finset.mem_image.mp hy with ⟨z, hz, hzy⟩
    subst y
    have hzq : z ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS hz))
    have hzx : z = x := by
      simpa [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_involutive hzq]
        using hyx
    simpa [hzx] using hz
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q x, ?_, ?_⟩
    · refine Finset.mem_image.mpr ?_
      exact ⟨x, hx, rfl⟩
    · have hxq : x ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS hx))
      exact paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_involutive hxq

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_sum
    {q k : ℕ} {S : Finset ℕ}
    (hS : S ∈ paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k) :
    Finset.sum
        (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q S)
        (fun i => i) =
      k * q - Finset.sum S (fun i => i) := by
  have hS' : S ∈ (Finset.range (q + 1)).powersetCard k := by
    simpa [paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family] using hS
  rw [Finset.mem_powersetCard] at hS'
  have hinj :
      Set.InjOn (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q) ↑S := by
    intro a ha b hb hab
    exact paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_injective q hab
  rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset, Finset.sum_image hinj]
  · have hrewrite :
        Finset.sum S
            (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index q) =
          Finset.sum S (fun i => q - i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS'.1 hi))
      simp [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index, hiq]
    rw [hrewrite, Finset.sum_tsub_distrib]
    · have hconst : Finset.sum S (fun _ => q) = S.card * q := by simp
      rw [hconst, hS'.2]
    · intro i hi
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (hS'.1 hi))

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer_eq_countP
    (q k s : ℕ) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k s =
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.countP
        fun S => s < Finset.sum S fun i => i) := by
  rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer,
    List.countP_eq_length_filter, ← Finset.length_toList
    ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter fun S =>
      s < Finset.sum S fun i => i)]
  have hnodupFilteredFinset :
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter
          fun S => s < Finset.sum S fun i => i).toList.Nodup :=
    Finset.nodup_toList
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter
        fun S => s < Finset.sum S fun i => i)
  have hnodupFilteredList :
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.filter
          fun S => s < Finset.sum S fun i => i).Nodup := by
    simpa using
      (Finset.nodup_toList
        (paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k)).filter
          (fun S => decide (s < Finset.sum S fun i => i))
  have hperm :
      List.Perm
        ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter
            fun S => s < Finset.sum S fun i => i).toList
        ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.filter
          fun S => s < Finset.sum S fun i => i) :=
    (List.perm_ext_iff_of_nodup hnodupFilteredFinset hnodupFilteredList).2 <| by
      intro T
      simp [Finset.mem_toList]
  exact hperm.length_eq

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_layer_eq_low_count
    (q k s : ℕ) (hs : s < k * q) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k (k * q - 1 - s) =
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter fun S =>
        (Finset.sum S fun i => i) ≤ s).card := by
  classical
  refine Finset.card_bij
    (fun S _ => paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q S)
    ?_ ?_ ?_
  · intro S hS
    refine Finset.mem_filter.mpr
      ⟨paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_mem_family
          ((Finset.mem_filter.mp hS).1), ?_⟩
    rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_sum
      ((Finset.mem_filter.mp hS).1)]
    have hgt := (Finset.mem_filter.mp hS).2
    omega
  · intro S _ T _ hST
    exact Finset.image_injective
      (paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_index_injective q) hST
  · intro T hT
    refine ⟨paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset q T, ?_, ?_⟩
    · refine Finset.mem_filter.mpr
        ⟨paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_mem_family
            ((Finset.mem_filter.mp hT).1), ?_⟩
      rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_sum
        ((Finset.mem_filter.mp hT).1)]
      have hle := (Finset.mem_filter.mp hT).2
      omega
    · exact paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_subset_involutive
        ((Finset.mem_powersetCard.mp ((Finset.mem_filter.mp hT).1)).1)

private lemma paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_law
    (q k s : ℕ) (hs : s < k * q) :
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k s +
        paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k
          (k * q - 1 - s) =
      Nat.choose (q + 1) k := by
  calc
    paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k s +
        paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer q k
          (k * q - 1 - s) =
      ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter fun S =>
          s < Finset.sum S fun i => i).card +
        ((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).filter
            fun S => (Finset.sum S fun i => i) ≤ s).card := by
          rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_layer_eq_low_count
            q k s hs, paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer]
    _ = (paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).card := by
          simpa [not_lt] using
            (Finset.card_filter_add_card_filter_not
              (s := paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k)
              (p := fun S : Finset ℕ => s < Finset.sum S fun i => i))
    _ = Nat.choose (q + 1) k := by
          simp [paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family]

/-- Paper label: `thm:derived-exterior-power-kernel-growth-hilbert-mirror`. -/
theorem paper_derived_exterior_power_kernel_growth_hilbert_mirror (q k : ℕ) :
    derived_exterior_power_kernel_growth_hilbert_mirror_statement q k := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rfl
  · intro s
    have hstep :=
      Omega.CircleDimension.FiniteProbeExtraction.paper_cdim_finite_probe_extraction_seeds
        (((paper_derived_exterior_power_kernel_growth_hilbert_mirror_subset_family q k).toList.map
          fun S => Finset.sum S fun i => i)) (s + 1) (Nat.succ_le_succ (Nat.zero_le s))
    rw [paper_derived_exterior_power_kernel_growth_hilbert_mirror_hilbert_layer_eq_countP]
    simpa [paper_derived_exterior_power_kernel_growth_hilbert_mirror_kernel_growth,
      List.countP_map, Nat.succ_le_iff] using hstep.symm
  · intro s hs
    exact paper_derived_exterior_power_kernel_growth_hilbert_mirror_mirror_law q k s hs

end
end Omega.DerivedConsequences
