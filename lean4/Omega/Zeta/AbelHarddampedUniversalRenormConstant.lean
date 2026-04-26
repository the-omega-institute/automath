import Mathlib

namespace Omega.Zeta

open Filter

noncomputable section

/-- A concrete base parameter for the damped Abel-Hardy energy package. -/
abbrev abel_harddamped_universal_renorm_constant_data := { b : ℝ // 1 < b }

def abel_harddamped_universal_renorm_constant_base
    (D : abel_harddamped_universal_renorm_constant_data) : ℝ := D.1

def abel_harddamped_universal_renorm_constant_zeroSumConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

def abel_harddamped_universal_renorm_constant_regularPart
    (D : abel_harddamped_universal_renorm_constant_data) (δ : ℝ) : ℝ :=
  δ / (1 + δ ^ 2) * abel_harddamped_universal_renorm_constant_base D

def abel_harddamped_universal_renorm_constant_energy
    (D : abel_harddamped_universal_renorm_constant_data) (δ : ℝ) : ℝ :=
  abel_harddamped_universal_renorm_constant_zeroSumConstant /
      (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) +
    abel_harddamped_universal_renorm_constant_regularPart D δ

def abel_harddamped_universal_renorm_constant_renormalizedEnergy
    (D : abel_harddamped_universal_renorm_constant_data) (δ : ℝ) : ℝ :=
  (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
    abel_harddamped_universal_renorm_constant_energy D δ

def abel_harddamped_universal_renorm_constant_statement
    (D : abel_harddamped_universal_renorm_constant_data) : Prop :=
  Tendsto (fun δ : ℝ =>
      abel_harddamped_universal_renorm_constant_renormalizedEnergy D δ)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds abel_harddamped_universal_renorm_constant_zeroSumConstant) ∧
    ∀ δ : ℝ, δ ≠ 0 →
      abel_harddamped_universal_renorm_constant_energy D δ =
        abel_harddamped_universal_renorm_constant_zeroSumConstant /
            (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) +
          abel_harddamped_universal_renorm_constant_regularPart D δ

theorem paper_abel_harddamped_universal_renorm_constant
    (D : abel_harddamped_universal_renorm_constant_data) :
    abel_harddamped_universal_renorm_constant_statement D := by
  constructor
  · have hbase_pos : 0 < abel_harddamped_universal_renorm_constant_base D :=
      lt_trans zero_lt_one D.2
    have hlog_pos : 0 < Real.log (abel_harddamped_universal_renorm_constant_base D) := by
      exact Real.log_pos D.2
    have hvanish :
        Tendsto
          (fun δ : ℝ =>
            (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
              abel_harddamped_universal_renorm_constant_regularPart D δ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hδ : Tendsto (fun δ : ℝ => δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      have hden :
          Tendsto (fun δ : ℝ => 1 + δ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (1 + 0 ^ 2)) :=
        (hδ.pow 2).const_add 1
      have hquot :
          Tendsto (fun δ : ℝ => δ / (1 + δ ^ 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (0 / (1 + 0 ^ 2))) :=
        hδ.div hden (by norm_num)
      have hreg :
          Tendsto
            (fun δ : ℝ =>
              abel_harddamped_universal_renorm_constant_regularPart D δ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa [abel_harddamped_universal_renorm_constant_regularPart] using
          hquot.mul tendsto_const_nhds
      have hscale :
          Tendsto
            (fun δ : ℝ =>
              2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using ((tendsto_const_nhds.mul hδ).mul tendsto_const_nhds)
      simpa using hscale.mul hreg
    have hpole :
        ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
              (abel_harddamped_universal_renorm_constant_zeroSumConstant /
                (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D))) =
            abel_harddamped_universal_renorm_constant_zeroSumConstant := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ
      field_simp [hδ_ne, hlog_pos.ne']
    have hmain :
        Tendsto
          (fun δ : ℝ =>
            (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
              (abel_harddamped_universal_renorm_constant_zeroSumConstant /
                (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds abel_harddamped_universal_renorm_constant_zeroSumConstant) :=
      (tendsto_congr' hpole).2 tendsto_const_nhds
    have hsum :
        Tendsto
          (fun δ : ℝ =>
            (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
                (abel_harddamped_universal_renorm_constant_zeroSumConstant /
                  (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D))) +
              (2 * δ * Real.log (abel_harddamped_universal_renorm_constant_base D)) *
                abel_harddamped_universal_renorm_constant_regularPart D δ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds abel_harddamped_universal_renorm_constant_zeroSumConstant) := by
      simpa using hmain.add hvanish
    convert hsum using 1
    ext δ
    simp [abel_harddamped_universal_renorm_constant_renormalizedEnergy,
      abel_harddamped_universal_renorm_constant_energy, mul_add]
  · intro δ _hδ
    rfl

end

end Omega.Zeta
