import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The normalized spectral gap `-log(ρ/λ)`. -/
noncomputable def conclusion_rho_m2_workload_max_decomposition_gap (lam ρ : ℝ) : ℝ :=
  -Real.log (ρ / lam)

/-- Workload at alphabet size `2m`, expressed as `log(2m)/Δ`. -/
noncomputable def conclusion_rho_m2_workload_max_decomposition_workload (m : ℕ)
    (Δ : ℝ) : ℝ :=
  Real.log (2 * (m : ℝ)) / Δ

/-- The anisotropy index after cancelling the common ambient scale `λ`. -/
noncomputable def conclusion_rho_m2_workload_max_decomposition_anisotropy
    (lam ρin ρbd : ℝ) : ℝ :=
  conclusion_rho_m2_workload_max_decomposition_gap lam ρbd -
    conclusion_rho_m2_workload_max_decomposition_gap lam ρin

private lemma conclusion_rho_m2_workload_max_decomposition_gap_le_of_rho_le
    {lam ρa ρb : ℝ} (hlam : 0 < lam) (ha : 0 < ρa) (hρ : ρa ≤ ρb) :
    conclusion_rho_m2_workload_max_decomposition_gap lam ρb ≤
      conclusion_rho_m2_workload_max_decomposition_gap lam ρa := by
  have hb : 0 < ρb := lt_of_lt_of_le ha hρ
  have hratio_le : ρa / lam ≤ ρb / lam := by
    exact div_le_div_of_nonneg_right hρ (le_of_lt hlam)
  have hlog_le : Real.log (ρa / lam) ≤ Real.log (ρb / lam) :=
    Real.log_le_log (div_pos ha hlam) hratio_le
  dsimp [conclusion_rho_m2_workload_max_decomposition_gap]
  linarith

private lemma conclusion_rho_m2_workload_max_decomposition_gap_lt_of_rho_lt
    {lam ρa ρb : ℝ} (hlam : 0 < lam) (ha : 0 < ρa) (hρ : ρa < ρb) :
    conclusion_rho_m2_workload_max_decomposition_gap lam ρb <
      conclusion_rho_m2_workload_max_decomposition_gap lam ρa := by
  have hb : 0 < ρb := lt_trans ha hρ
  have hratio_lt : ρa / lam < ρb / lam := by
    exact div_lt_div_of_pos_right hρ hlam
  have hlog_lt : Real.log (ρa / lam) < Real.log (ρb / lam) :=
    Real.log_lt_log (div_pos ha hlam) hratio_lt
  dsimp [conclusion_rho_m2_workload_max_decomposition_gap]
  linarith

private lemma conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
    {c Δa Δb : ℝ} (hc : 0 < c) (ha : 0 < Δa) (hb : 0 < Δb) :
    c / Δa > c / Δb ↔ Δa < Δb := by
  constructor
  · intro hwork
    by_contra hnot
    have hle : Δb ≤ Δa := le_of_not_gt hnot
    have hinv : Δa⁻¹ ≤ Δb⁻¹ := by
      rw [inv_le_inv₀ ha hb]
      exact hle
    have hwork_le : c / Δa ≤ c / Δb := by
      have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt hc)
      simpa [div_eq_mul_inv] using hmul
    exact (not_lt_of_ge hwork_le) hwork
  · intro hgap
    have hinv : Δb⁻¹ < Δa⁻¹ := by
      rw [inv_lt_inv₀ hb ha]
      exact hgap
    have hmul := mul_lt_mul_of_pos_left hinv hc
    simpa [div_eq_mul_inv] using hmul

private lemma conclusion_rho_m2_workload_max_decomposition_workload_lt_iff
    {c Δa Δb : ℝ} (hc : 0 < c) (ha : 0 < Δa) (hb : 0 < Δb) :
    c / Δa < c / Δb ↔ Δb < Δa := by
  simpa [gt_iff_lt] using
    (conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
      (c := c) (Δa := Δb) (Δb := Δa) hc hb ha)

private lemma conclusion_rho_m2_workload_max_decomposition_workload_eq_iff
    {c Δa Δb : ℝ} (hc : 0 < c) (ha : 0 < Δa) (hb : 0 < Δb) :
    c / Δa = c / Δb ↔ Δa = Δb := by
  constructor
  · intro hwork
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hwgt : c / Δa > c / Δb :=
        (conclusion_rho_m2_workload_max_decomposition_workload_gt_iff hc ha hb).2 hlt
      linarith
    · have hwlt : c / Δa < c / Δb :=
        (conclusion_rho_m2_workload_max_decomposition_workload_lt_iff hc ha hb).2 hgt
      linarith
  · intro hgap
    rw [hgap]

/-- Paper label: `cor:conclusion-rho-m2-workload-max-decomposition`. If the combined radius is the
maximum of the interior and boundary radii, then `-log` turns the bottleneck into the minimum gap,
and positive reciprocal scaling turns that minimum gap into the maximum workload. The gap-form
anisotropy index has the same sign as the workload imbalance. -/
theorem paper_conclusion_rho_m2_workload_max_decomposition (m : ℕ) (hm : 1 ≤ m)
    (lam ρ ρin ρbd : ℝ) (hlam : 0 < lam) (hin : 0 < ρin) (hbd : 0 < ρbd)
    (hΔin : 0 < conclusion_rho_m2_workload_max_decomposition_gap lam ρin)
    (hΔbd : 0 < conclusion_rho_m2_workload_max_decomposition_gap lam ρbd)
    (hrho : ρ = max ρin ρbd) :
    conclusion_rho_m2_workload_max_decomposition_gap lam ρ =
        min (conclusion_rho_m2_workload_max_decomposition_gap lam ρin)
          (conclusion_rho_m2_workload_max_decomposition_gap lam ρbd) ∧
      conclusion_rho_m2_workload_max_decomposition_workload m
          (conclusion_rho_m2_workload_max_decomposition_gap lam ρ) =
        max
          (conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρin))
          (conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρbd)) ∧
      (0 < conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd ↔
        conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρin) >
          conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρbd)) ∧
      (conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd < 0 ↔
        conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρin) <
          conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρbd)) ∧
      (conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd = 0 ↔
        conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρin) =
          conclusion_rho_m2_workload_max_decomposition_workload m
            (conclusion_rho_m2_workload_max_decomposition_gap lam ρbd)) := by
  let Δin := conclusion_rho_m2_workload_max_decomposition_gap lam ρin
  let Δbd := conclusion_rho_m2_workload_max_decomposition_gap lam ρbd
  let c := Real.log (2 * (m : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    apply Real.log_pos
    have hm_real : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hgap_min :
      conclusion_rho_m2_workload_max_decomposition_gap lam ρ = min Δin Δbd := by
    by_cases hle : ρin ≤ ρbd
    · have hmax : max ρin ρbd = ρbd := max_eq_right hle
      have hgap_le : Δbd ≤ Δin :=
        conclusion_rho_m2_workload_max_decomposition_gap_le_of_rho_le hlam hin hle
      have hmin : min Δin Δbd = Δbd := min_eq_right hgap_le
      simp [Δin, Δbd, hrho, hmax, hmin]
    · have hle' : ρbd ≤ ρin := le_of_lt (lt_of_not_ge hle)
      have hmax : max ρin ρbd = ρin := max_eq_left hle'
      have hgap_le : Δin ≤ Δbd :=
        conclusion_rho_m2_workload_max_decomposition_gap_le_of_rho_le hlam hbd hle'
      have hmin : min Δin Δbd = Δin := min_eq_left hgap_le
      simp [Δin, Δbd, hrho, hmax, hmin]
  have hwork_max :
      conclusion_rho_m2_workload_max_decomposition_workload m
          (conclusion_rho_m2_workload_max_decomposition_gap lam ρ) =
        max (conclusion_rho_m2_workload_max_decomposition_workload m Δin)
          (conclusion_rho_m2_workload_max_decomposition_workload m Δbd) := by
    by_cases hle : Δin ≤ Δbd
    · have hmin : min Δin Δbd = Δin := min_eq_left hle
      have hwork_ge :
          conclusion_rho_m2_workload_max_decomposition_workload m Δbd ≤
            conclusion_rho_m2_workload_max_decomposition_workload m Δin := by
        have hgt_or_eq : Δin < Δbd ∨ Δin = Δbd := lt_or_eq_of_le hle
        rcases hgt_or_eq with hlt | heq
        · exact le_of_lt
            ((conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
              (c := c) (Δa := Δin) (Δb := Δbd) hc
              (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).2 hlt)
        · simp [conclusion_rho_m2_workload_max_decomposition_workload, heq]
      rw [hgap_min, hmin, max_eq_left hwork_ge]
    · have hle' : Δbd ≤ Δin := le_of_lt (lt_of_not_ge hle)
      have hmin : min Δin Δbd = Δbd := min_eq_right hle'
      have hwork_ge :
          conclusion_rho_m2_workload_max_decomposition_workload m Δin ≤
            conclusion_rho_m2_workload_max_decomposition_workload m Δbd := by
        have hgt_or_eq : Δbd < Δin ∨ Δbd = Δin := lt_or_eq_of_le hle'
        rcases hgt_or_eq with hlt | heq
        · exact le_of_lt
            ((conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
              (c := c) (Δa := Δbd) (Δb := Δin) hc
              (by simpa [Δbd] using hΔbd) (by simpa [Δin] using hΔin)).2 hlt)
        · simp [conclusion_rho_m2_workload_max_decomposition_workload, heq]
      rw [hgap_min, hmin, max_eq_right hwork_ge]
  have hpos_iff :
      0 < conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd ↔
        conclusion_rho_m2_workload_max_decomposition_workload m Δin >
          conclusion_rho_m2_workload_max_decomposition_workload m Δbd := by
    constructor
    · intro hA
      have hlt : Δin < Δbd := by
        dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd] at hA
        linarith
      exact (conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
        (c := c) (Δa := Δin) (Δb := Δbd) hc
        (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).2 hlt
    · intro hW
      have hlt : Δin < Δbd :=
        (conclusion_rho_m2_workload_max_decomposition_workload_gt_iff
          (c := c) (Δa := Δin) (Δb := Δbd) hc
          (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).1 hW
      dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd]
      linarith
  have hneg_iff :
      conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd < 0 ↔
        conclusion_rho_m2_workload_max_decomposition_workload m Δin <
          conclusion_rho_m2_workload_max_decomposition_workload m Δbd := by
    constructor
    · intro hA
      have hlt : Δbd < Δin := by
        dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd] at hA
        linarith
      exact (conclusion_rho_m2_workload_max_decomposition_workload_lt_iff
        (c := c) (Δa := Δin) (Δb := Δbd) hc
        (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).2 hlt
    · intro hW
      have hlt : Δbd < Δin :=
        (conclusion_rho_m2_workload_max_decomposition_workload_lt_iff
          (c := c) (Δa := Δin) (Δb := Δbd) hc
          (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).1 hW
      dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd]
      linarith
  have heq_iff :
      conclusion_rho_m2_workload_max_decomposition_anisotropy lam ρin ρbd = 0 ↔
        conclusion_rho_m2_workload_max_decomposition_workload m Δin =
          conclusion_rho_m2_workload_max_decomposition_workload m Δbd := by
    constructor
    · intro hA
      have heq : Δin = Δbd := by
        dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd] at hA
        linarith
      simp [heq]
    · intro hW
      have heq : Δin = Δbd :=
        (conclusion_rho_m2_workload_max_decomposition_workload_eq_iff
          (c := c) (Δa := Δin) (Δb := Δbd) hc
          (by simpa [Δin] using hΔin) (by simpa [Δbd] using hΔbd)).1 hW
      dsimp [conclusion_rho_m2_workload_max_decomposition_anisotropy, Δin, Δbd]
      linarith
  exact ⟨hgap_min, hwork_max, by simpa [Δin, Δbd] using hpos_iff,
    by simpa [Δin, Δbd] using hneg_iff, by simpa [Δin, Δbd] using heq_iff⟩

end Omega.Conclusion
