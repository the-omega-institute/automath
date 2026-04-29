import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Zeta

private lemma xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMStep_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMStep (2 * w * q) w = 2 * q := by
  unfold Omega.Folding.sgMStep
  have hdiv : w ∣ 2 * w * q := ⟨2 * q, by ring⟩
  rw [Nat.gcd_eq_right hdiv]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_div_right (2 * q) hw

private lemma xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMBase_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMBase (2 * w * q) w = q := by
  unfold Omega.Folding.sgMBase
  rw [xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMStep_factor hw]
  simp

private lemma
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMFrequencySet (2 * w * q) w =
      (Finset.range w).image (fun k => q + k * (2 * q)) := by
  unfold Omega.Folding.sgMFrequencySet
  have hdiv : w ∣ 2 * w * q := ⟨2 * q, by ring⟩
  rw [Nat.gcd_eq_right hdiv,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMBase_factor hw,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMStep_factor hw]

private lemma
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_base_mem_self
    {M g : ℕ} (hM : 0 < M) (hEven : Even M) (hg : 0 < g) (hgdiv : g ∣ M / 2) :
    Omega.Folding.sgMBase M g ∈ Omega.Folding.sgMFrequencySet M g := by
  rcases hEven with ⟨t, rfl⟩
  have hhalf : (t + t) / 2 = t := by omega
  rw [hhalf] at hgdiv
  rcases hgdiv with ⟨q, hq⟩
  have hrepr : t + t = 2 * g * q := by
    rw [hq]
    ring
  rw [hrepr,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMBase_factor hg,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hg]
  apply Finset.mem_image.mpr
  refine ⟨0, by simpa using hg, by simp⟩

private lemma
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_subset_of_dvd_odd
    {M g h : ℕ} (hEven : Even M) (hg : 0 < g) (hh : 0 < h) (hhdiv : h ∣ M / 2)
    (hgh : g ∣ h) (hodd : Odd (h / g)) :
    Omega.Folding.sgMFrequencySet M g ⊆ Omega.Folding.sgMFrequencySet M h := by
  rcases hgh with ⟨d, rfl⟩
  rcases hodd with ⟨m, hm⟩
  have hd : d = 2 * m + 1 := by
    simpa [Nat.mul_div_right _ hg] using hm
  rcases hEven with ⟨t, rfl⟩
  have hhalf : (t + t) / 2 = t := by omega
  rw [hhalf] at hhdiv
  rcases hhdiv with ⟨q, hq⟩
  have hreprg : t + t = 2 * g * ((2 * m + 1) * q) := by
    rw [hq, hd]
    ring
  have hreprh : t + t = 2 * (g * d) * q := by
    rw [hq]
    ring
  intro x hx
  rw [hreprg,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hg] at hx
  rw [hreprh,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hh]
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨m + k * (2 * m + 1), ?_, ?_⟩
  · have hk' : k < g := by simpa [hd] using hk
    have hm_lt : m < 2 * m + 1 := by omega
    simpa using
      (calc
        m + k * (2 * m + 1) < (2 * m + 1) + k * (2 * m + 1) := by gcongr
        _ = (k + 1) * (2 * m + 1) := by ring
        _ ≤ g * (2 * m + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hk')
        _ = g * d := by rw [hd])
  · ring

private lemma
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_base_mem_implies_odd
    {M g h : ℕ} (hM : 0 < M) (hEven : Even M) (hg : 0 < g) (hh : 0 < h)
    (hgdiv : g ∣ M / 2) (hhdiv : h ∣ M / 2)
    (hmem : Omega.Folding.sgMBase M g ∈ Omega.Folding.sgMFrequencySet M h) :
    Odd (h / g) := by
  rcases hEven with ⟨t, rfl⟩
  have hhalf : (t + t) / 2 = t := by omega
  rw [hhalf] at hgdiv hhdiv
  rcases hgdiv with ⟨a, ha⟩
  rcases hhdiv with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    by_contra hq0
    have hq0' : q = 0 := Nat.eq_zero_of_not_pos hq0
    have : t = 0 := by simpa [hq0'] using hq
    omega
  have hreprg : t + t = 2 * g * a := by
    rw [ha]
    ring
  have hreprh : t + t = 2 * h * q := by
    rw [hq]
    ring
  have hbase :
      Omega.Folding.sgMBase (t + t) g = a := by
    rw [hreprg,
      xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMBase_factor hg]
  have hfreq :
      Omega.Folding.sgMFrequencySet (t + t) h =
        (Finset.range h).image (fun k => q + k * (2 * q)) := by
    rw [hreprh,
      xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hh]
  have hmem' := hmem
  rw [hbase, hfreq] at hmem'
  rcases Finset.mem_image.mp hmem' with ⟨k, _hk, hkEq⟩
  have haEq : a = (2 * k + 1) * q := by
    calc
      a = q + k * (2 * q) := by simpa using hkEq.symm
      _ = (2 * k + 1) * q := by ring
  have hmul : h * q = g * ((2 * k + 1) * q) := by
    calc
      h * q = t := by rw [hq]
      _ = g * a := by rw [ha]
      _ = g * ((2 * k + 1) * q) := by rw [haEq]
  have hrepr : h = g * (2 * k + 1) := by
    exact Nat.eq_of_mul_eq_mul_right hq_pos (by simpa [Nat.mul_assoc] using hmul)
  rw [hrepr, Nat.mul_div_right _ hg]
  exact ⟨k, rfl⟩

private lemma
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_disjoint_of_even_quotient
    {M g h : ℕ} (hM : 0 < M) (hEven : Even M) (hg : 0 < g) (hh : 0 < h)
    (hhdiv : h ∣ M / 2) (hgh : g ∣ h) (heven : Even (h / g)) :
    Omega.Folding.sgMFrequencySet M g ∩ Omega.Folding.sgMFrequencySet M h = ∅ := by
  rcases hgh with ⟨d, rfl⟩
  have hd_eq : g * d / g = d := Nat.mul_div_right d hg
  have hd_even : Even d := by simpa [hd_eq] using heven
  rcases hd_even with ⟨r, hr⟩
  rcases hEven with ⟨t, rfl⟩
  have hhalf : (t + t) / 2 = t := by omega
  rw [hhalf] at hhdiv
  rcases hhdiv with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    by_contra hq0
    have hq0' : q = 0 := Nat.eq_zero_of_not_pos hq0
    have : t = 0 := by simpa [hq0'] using hq
    omega
  have hreprg : t + t = 2 * g * (d * q) := by
    rw [hq]
    ring
  have hreprh : t + t = 2 * (g * d) * q := by
    rw [hq]
    ring
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxg : x ∈ Omega.Folding.sgMFrequencySet (t + t) g := (Finset.mem_inter.mp hx).1
  have hxh : x ∈ Omega.Folding.sgMFrequencySet (t + t) (g * d) := (Finset.mem_inter.mp hx).2
  rw [hreprg,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hg] at hxg
  rw [hreprh,
    xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_sgMFrequencySet_factor hh] at hxh
  rcases Finset.mem_image.mp hxg with ⟨k, _hk, hkEq⟩
  rcases Finset.mem_image.mp hxh with ⟨l, _hl, hlEq⟩
  have hcancel :
      (2 * k + 1) * d = 2 * l + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hq_pos
    calc
      ((2 * k + 1) * d) * q = d * q + k * (2 * (d * q)) := by ring
      _ = x := by simpa using hkEq
      _ = q + l * (2 * q) := by simpa using hlEq.symm
      _ = (2 * l + 1) * q := by ring
  have hleft_even : Even ((2 * k + 1) * d) := by
    rw [hr]
    exact ⟨(2 * k + 1) * r, by ring⟩
  have hright_odd : Odd (2 * l + 1) := ⟨l, rfl⟩
  have hcontr : Even (2 * l + 1) := by
    rw [← hcancel]
    exact hleft_even
  exact (Nat.not_even_iff_odd.mpr hright_odd) hcontr

/-- Paper label: `thm:xi-time-part72-zero-coset-divisibility-nested-disjoint-dichotomy`. -/
theorem paper_xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy
    (M g h : ℕ) (hM : 0 < M) (hEven : Even M) (hgpos : 0 < g) (hhpos : 0 < h)
    (hg : g ∣ M / 2) (hh : h ∣ M / 2) (hgh : g ∣ h) :
    ((Omega.Folding.sgMFrequencySet M g ⊆ Omega.Folding.sgMFrequencySet M h) ↔
        Odd (h / g)) ∧
      (Even (h / g) →
        Omega.Folding.sgMFrequencySet M g ∩ Omega.Folding.sgMFrequencySet M h = ∅) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hsubset
      exact
        xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_base_mem_implies_odd
          hM hEven hgpos hhpos hg hh
          (hsubset
            (xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_base_mem_self
              hM hEven hgpos hg))
    · intro hodd
      exact
        xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_subset_of_dvd_odd
          hEven hgpos hhpos hh hgh hodd
  · intro heven
    exact
      xi_time_part72_zero_coset_divisibility_nested_disjoint_dichotomy_disjoint_of_even_quotient
        hM hEven hgpos hhpos hh hgh heven

end Omega.Zeta
