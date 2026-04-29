import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter

namespace Omega.POM

/-- Concrete top-stratum data for the diagonal subleading expansion. The partition sum is written
as the dominant contribution `N_m exp(q_m log M_m)` times `1 + r_m`, where `r_m` is the
complement-to-top ratio. The top-degeneracy exponent is encoded by the limit of `log N_m / m`. -/
structure DiagonalSubleadingTopDegeneracyData where
  q : ℕ → ℕ
  topMultiplicity : ℕ → ℝ
  topDegeneracy : ℕ → ℝ
  complementRatio : ℕ → ℝ
  topDegeneracyExponent : ℝ
  gap : ℝ
  topMultiplicity_pos : ∀ m, 0 < topMultiplicity m
  topDegeneracy_pos : ∀ m, 0 < topDegeneracy m
  complementRatio_nonneg : ∀ m, 0 ≤ complementRatio m
  complementRatio_tendsto :
    Tendsto complementRatio atTop (nhds 0)
  complementRatio_exponential :
    ∀ m, complementRatio m ≤ Real.exp (-gap * (m : ℝ) ^ (2 : ℕ))
  topDegeneracy_log_limit :
    Tendsto (fun m => Real.log (topDegeneracy m) / (m : ℝ)) atTop
      (nhds topDegeneracyExponent)

namespace DiagonalSubleadingTopDegeneracyData

/-- The top-stratum contribution `N_m M_m^{q_m}`, written as `N_m exp(q_m log M_m)` so that the
logarithm is exact without extra power lemmas. -/
noncomputable def topStratumTerm (D : DiagonalSubleadingTopDegeneracyData) (m : ℕ) : ℝ :=
  D.topDegeneracy m * Real.exp ((D.q m : ℝ) * Real.log (D.topMultiplicity m))

/-- The full partition sum after adding the complement contribution relative to the top stratum. -/
noncomputable def partitionSum (D : DiagonalSubleadingTopDegeneracyData) (m : ℕ) : ℝ :=
  D.topStratumTerm m * (1 + D.complementRatio m)

/-- The `o(1)` logarithmic expansion after splitting off the top stratum. -/
def leadingExpansion (D : DiagonalSubleadingTopDegeneracyData) : Prop :=
  ∃ err : ℕ → ℝ,
    Tendsto err atTop (nhds 0) ∧
      ∀ m,
        Real.log (D.partitionSum m) =
          Real.log (D.topDegeneracy m) +
            (D.q m : ℝ) * Real.log (D.topMultiplicity m) + err m

/-- After subtracting the leading `q_m log M_m` term and dividing by `m`, the limit is the top
degeneracy exponent carried by `log N_m / m`. -/
def subleadingLimit (D : DiagonalSubleadingTopDegeneracyData) : Prop :=
  Tendsto
      (fun m =>
        (Real.log (D.partitionSum m) - (D.q m : ℝ) * Real.log (D.topMultiplicity m)) /
          (m : ℝ))
      atTop
      (nhds D.topDegeneracyExponent)

end DiagonalSubleadingTopDegeneracyData

open DiagonalSubleadingTopDegeneracyData

/-- Paper label: `thm:pom-diagonal-subleading-top-degeneracy`. -/
theorem paper_pom_diagonal_subleading_top_degeneracy (D : DiagonalSubleadingTopDegeneracyData) :
    D.leadingExpansion ∧ D.subleadingLimit := by
  let err : ℕ → ℝ := fun m => Real.log (1 + D.complementRatio m)
  have herr : Tendsto err atTop (nhds 0) := by
    have hOnePlus : Tendsto (fun m => 1 + D.complementRatio m) atTop (nhds (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.add D.complementRatio_tendsto)
    have hlog : Tendsto (fun x : ℝ => Real.log x) (nhds (1 : ℝ)) (nhds (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa [err, Real.log_one] using hlog.comp hOnePlus
  have hleading :
      ∀ m,
        Real.log (D.partitionSum m) =
          Real.log (D.topDegeneracy m) +
            (D.q m : ℝ) * Real.log (D.topMultiplicity m) + err m := by
    intro m
    have hdeg : 0 < D.topDegeneracy m := D.topDegeneracy_pos m
    have hmul : 0 < D.topMultiplicity m := D.topMultiplicity_pos m
    have hratio : 0 < 1 + D.complementRatio m := by
      linarith [D.complementRatio_nonneg m]
    have htop :
        0 < D.topStratumTerm m := by
      unfold DiagonalSubleadingTopDegeneracyData.topStratumTerm
      positivity
    calc
      Real.log (D.partitionSum m)
          = Real.log (D.topStratumTerm m) + Real.log (1 + D.complementRatio m) := by
              unfold DiagonalSubleadingTopDegeneracyData.partitionSum
              rw [Real.log_mul (ne_of_gt htop) (ne_of_gt hratio)]
      _ = (Real.log (D.topDegeneracy m) +
            Real.log (Real.exp ((D.q m : ℝ) * Real.log (D.topMultiplicity m)))) +
            Real.log (1 + D.complementRatio m) := by
              unfold DiagonalSubleadingTopDegeneracyData.topStratumTerm
              rw [Real.log_mul (ne_of_gt hdeg) (by positivity : Real.exp _ ≠ 0)]
      _ = Real.log (D.topDegeneracy m) +
            (D.q m : ℝ) * Real.log (D.topMultiplicity m) + err m := by
              simp [err, add_assoc, add_comm]
  have hsub :
    Tendsto
      (fun m =>
        (Real.log (D.partitionSum m) - (D.q m : ℝ) * Real.log (D.topMultiplicity m)) /
          (m : ℝ))
      atTop
      (nhds D.topDegeneracyExponent) := by
    have herr_div : Tendsto (fun m : ℕ => err m / (m : ℝ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹)) atTop (nhds (0 : ℝ)) := by
        exact (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (nhds (0 : ℝ))).comp
          tendsto_natCast_atTop_atTop
      have hmul : Tendsto (fun m : ℕ => err m * ((m : ℝ)⁻¹)) atTop (nhds (0 * 0)) :=
        herr.mul hinv
      simpa [div_eq_mul_inv] using hmul
    have hrewrite :
        (fun m =>
          (Real.log (D.partitionSum m) - (D.q m : ℝ) * Real.log (D.topMultiplicity m)) /
            (m : ℝ)) =
          fun m => Real.log (D.topDegeneracy m) / (m : ℝ) + err m / (m : ℝ) := by
      funext m
      calc
        (Real.log (D.partitionSum m) - (D.q m : ℝ) * Real.log (D.topMultiplicity m)) /
            (m : ℝ)
            =
            ((Real.log (D.topDegeneracy m) +
                (D.q m : ℝ) * Real.log (D.topMultiplicity m) + err m) -
              (D.q m : ℝ) * Real.log (D.topMultiplicity m)) / (m : ℝ) := by
                rw [hleading m]
        _ = (Real.log (D.topDegeneracy m) + err m) / (m : ℝ) := by ring
        _ = Real.log (D.topDegeneracy m) / (m : ℝ) + err m / (m : ℝ) := by
              rw [add_div]
    rw [hrewrite]
    simpa [zero_add] using D.topDegeneracy_log_limit.add herr_div
  exact ⟨⟨err, herr, hleading⟩, hsub⟩

end Omega.POM
