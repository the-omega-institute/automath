import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Zeta

/-- The maximal generators for odd-divisibility compression. -/
def xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_maximal
    (G : Finset ℕ) : Finset ℕ :=
  G.filter (fun g => ∀ h ∈ G, g ∣ h → Odd (h / g) → h = g)

private lemma xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMStep_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMStep (2 * w * q) w = 2 * q := by
  unfold Omega.Folding.sgMStep
  have hdiv : w ∣ 2 * w * q := ⟨2 * q, by ring⟩
  rw [Nat.gcd_eq_right hdiv]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_div_right (2 * q) hw

private lemma xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMBase_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMBase (2 * w * q) w = q := by
  unfold Omega.Folding.sgMBase
  rw [xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMStep_factor hw]
  simp

private lemma
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMFrequencySet_factor
    {w q : ℕ} (hw : 0 < w) :
    Omega.Folding.sgMFrequencySet (2 * w * q) w =
      (Finset.range w).image (fun k => q + k * (2 * q)) := by
  unfold Omega.Folding.sgMFrequencySet
  have hdiv : w ∣ 2 * w * q := ⟨2 * q, by ring⟩
  rw [Nat.gcd_eq_right hdiv,
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMBase_factor hw,
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMStep_factor hw]

private lemma
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_base_mem_self
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
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMBase_factor hg,
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMFrequencySet_factor hg]
  apply Finset.mem_image.mpr
  refine ⟨0, by simpa using hg, by simp⟩

private lemma
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_subset_of_dvd_odd
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
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMFrequencySet_factor hg] at hx
  rw [hreprh,
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMFrequencySet_factor hh]
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
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_base_mem_implies_dvd_odd
    {M g h : ℕ} (hM : 0 < M) (hEven : Even M) (hg : 0 < g) (hh : 0 < h)
    (hgdiv : g ∣ M / 2) (hhdiv : h ∣ M / 2)
    (hmem : Omega.Folding.sgMBase M g ∈ Omega.Folding.sgMFrequencySet M h) :
    g ∣ h ∧ Odd (h / g) := by
  rcases hEven with ⟨t, rfl⟩
  have hhalf : (t + t) / 2 = t := by omega
  rw [hhalf] at hgdiv hhdiv
  rcases hgdiv with ⟨a, ha⟩
  rcases hhdiv with ⟨q, hq⟩
  have ht_pos : 0 < t := by omega
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
      xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMBase_factor hg]
  have hfreq :
      Omega.Folding.sgMFrequencySet (t + t) h =
        (Finset.range h).image (fun k => q + k * (2 * q)) := by
    rw [hreprh,
      xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_sgMFrequencySet_factor hh]
  have hmem' := hmem
  rw [hbase, hfreq] at hmem'
  rcases Finset.mem_image.mp hmem' with ⟨k, hk, hkEq⟩
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
  refine ⟨⟨2 * k + 1, hrepr⟩, ?_⟩
  rw [hrepr, Nat.mul_div_right _ hg]
  exact ⟨k, rfl⟩

private lemma
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_exists_maximal_above
    {M : ℕ} {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g ∧ g ∣ M / 2) {g : ℕ} (hgG : g ∈ G) :
    ∃ m ∈ xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_maximal G,
      g ∣ m ∧ Odd (m / g) := by
  classical
  let C := G.filter (fun h => g ∣ h ∧ Odd (h / g))
  have hgpos : 0 < g := (hG g hgG).1
  have hC_nonempty : C.Nonempty := by
    refine ⟨g, by simp [C, hgG, Nat.div_self hgpos]⟩
  let m := C.max' hC_nonempty
  have hmC : m ∈ C := Finset.max'_mem C hC_nonempty
  have hmG : m ∈ G := by
    simp [C] at hmC
    exact hmC.1
  have hgm : g ∣ m ∧ Odd (m / g) := by
    simp [C] at hmC
    exact hmC.2
  refine ⟨m, ?_, hgm⟩
  refine Finset.mem_filter.mpr ⟨hmG, ?_⟩
  intro h hhG hmdiv hodd
  by_contra hne
  have hgh : g ∣ h := dvd_trans hgm.1 hmdiv
  have hmdiv_dvd := hmdiv
  rcases hgm.1 with ⟨u, hu⟩
  rcases hmdiv with ⟨v, hv⟩
  have huodd : Odd u := by
    simpa [hu, Nat.mul_div_right _ hgpos] using hgm.2
  have hvodd : Odd v := by
    simpa [hv, Nat.mul_div_right _ (hG m hmG).1] using hodd
  have hrepr : h = g * (u * v) := by
    rw [hv, hu]
    ring
  have hodd' : Odd (h / g) := by
    have hquot : h / g = u * v := by
      rw [hrepr, Nat.mul_div_right _ hgpos]
    simpa [hquot] using huodd.mul hvodd
  have hhC : h ∈ C := by
    simp [C, hhG, hgh, hodd']
  have hle : h ≤ m := Finset.le_max' C h hhC
  have hmle : m ≤ h := Nat.le_of_dvd (hG h hhG).1 hmdiv_dvd
  exact hne (le_antisymm hle hmle)

/-- Paper label: `thm:xi-time-part72a-zero-spectrum-maximal-odd-divisibility-compression`. After
adding the missing positivity and evenness hypotheses on `M`, removing every non-maximal odd
multiple does not change the union of zero-cosets, and the maximal family is the unique minimal
generating subfamily. -/
theorem paper_xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression
    (M : ℕ) (G : Finset ℕ) (hM : 0 < M) (hEven : Even M)
    (hG : ∀ g ∈ G, 0 < g ∧ g ∣ M / 2) :
    let maximal :=
      xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_maximal G
    (⋃ g ∈ G, (↑(Omega.Folding.sgMFrequencySet M g) : Set ℕ)) =
      ⋃ g ∈ maximal, (↑(Omega.Folding.sgMFrequencySet M g) : Set ℕ) ∧
    ∀ A : Finset ℕ, A ⊆ G →
      (⋃ g ∈ G, (↑(Omega.Folding.sgMFrequencySet M g) : Set ℕ)) =
        ⋃ g ∈ A, (↑(Omega.Folding.sgMFrequencySet M g) : Set ℕ) →
      maximal ⊆ A := by
  classical
  dsimp
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp at hx ⊢
      rcases hx with ⟨g, hgG, hxg⟩
      rcases
          xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_exists_maximal_above
            (M := M) (G := G) hG hgG with
        ⟨m, hmMax, hgm, hodd⟩
      have hmG : m ∈ G := (Finset.mem_filter.mp hmMax).1
      have hxm :
          x ∈ Omega.Folding.sgMFrequencySet M m :=
        xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_subset_of_dvd_odd
            hEven (hG g hgG).1 (hG m hmG).1 (hG m hmG).2 hgm hodd hxg
      exact ⟨m, hmMax, hxm⟩
    · intro hx
      simp at hx ⊢
      rcases hx with ⟨g, hgMax, hxg⟩
      exact ⟨g, (Finset.mem_filter.mp hgMax).1, hxg⟩
  · intro A hA hEq g hgMax
    have hgG : g ∈ G := (Finset.mem_filter.mp hgMax).1
    have hgpos : 0 < g := (hG g hgG).1
    have hgdiv : g ∣ M / 2 := (hG g hgG).2
    have hbaseG :
        Omega.Folding.sgMBase M g ∈
          (⋃ h ∈ G, (↑(Omega.Folding.sgMFrequencySet M h) : Set ℕ)) := by
      have hbaseG' :
          ∃ i, i ∈ G ∧ Omega.Folding.sgMBase M g ∈ Omega.Folding.sgMFrequencySet M i := by
        refine ⟨g, hgG, ?_⟩
        exact
          xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_base_mem_self
            hM hEven hgpos hgdiv
      simpa using hbaseG'
    have hbaseA :
        Omega.Folding.sgMBase M g ∈
          (⋃ h ∈ A, (↑(Omega.Folding.sgMFrequencySet M h) : Set ℕ)) := by
      rw [hEq] at hbaseG
      exact hbaseG
    simp at hbaseA
    rcases hbaseA with ⟨a, haA, hmem⟩
    have haG : a ∈ G := hA haA
    have hadv :
        g ∣ a ∧ Odd (a / g) :=
      xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_base_mem_implies_dvd_odd
        hM hEven hgpos (hG a haG).1 hgdiv (hG a haG).2 hmem
    have hag : a = g := (Finset.mem_filter.mp hgMax).2 a haG hadv.1 hadv.2
    simpa [hag] using haA

end Omega.Zeta
