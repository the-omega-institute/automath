import Mathlib

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

/-- Concrete pressure data for the multiplicative-ray gap identity. -/
structure XiTimePart65hPressureGapRayPotentialData where
  pressure : ℕ → ℝ
  escortRenyiEntropy : ℕ → ℕ → ℝ
  alphaStar : ℝ
  escortRenyiIdentity :
    ∀ a b, 1 ≤ a → 2 ≤ b →
      escortRenyiEntropy a b = (b * pressure a - pressure (a * b)) / (b - 1)
  escortRenyiNonneg :
    ∀ a b, 1 ≤ a → 2 ≤ b → 0 ≤ escortRenyiEntropy a b
  rayPressureRatioLimit :
    ∀ a b, 1 ≤ a → 2 ≤ b →
      Tendsto (fun N => pressure (a * b ^ N) / ((a * b ^ N : ℕ) : ℝ)) atTop (𝓝 alphaStar)

namespace XiTimePart65hPressureGapRayPotentialData

noncomputable def delta (D : XiTimePart65hPressureGapRayPotentialData) (a : ℕ) : ℝ :=
  D.pressure a / (a : ℝ) - D.alphaStar

noncomputable def pressureLoss (D : XiTimePart65hPressureGapRayPotentialData) (a b : ℕ) : ℝ :=
  (b : ℝ) * D.pressure a - D.pressure (a * b)

noncomputable def rayTerm (D : XiTimePart65hPressureGapRayPotentialData) (a b k : ℕ) : ℝ :=
  D.pressureLoss (a * b ^ k) b / ((a * b ^ (k + 1) : ℕ) : ℝ)

noncomputable def rayPartialSum (D : XiTimePart65hPressureGapRayPotentialData)
    (a b N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun k => D.rayTerm a b k)

/-- The pressure-gap identity, its escort-Rényi reformulation, the induced nonnegativity, and the
telescoping ray expansion. -/
def pressureGapRayPotential (D : XiTimePart65hPressureGapRayPotentialData) : Prop :=
  ∀ a b, 1 ≤ a → 2 ≤ b →
    D.delta a - D.delta (a * b) = D.pressureLoss a b / ((a * b : ℕ) : ℝ) ∧
      D.delta a - D.delta (a * b) =
        (((b - 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)) * D.escortRenyiEntropy a b ∧
      0 ≤ D.delta a - D.delta (a * b) ∧
      Tendsto (D.rayPartialSum a b) atTop (𝓝 (D.delta a))

end XiTimePart65hPressureGapRayPotentialData

open XiTimePart65hPressureGapRayPotentialData

private lemma delta_gap_eq_pressureLoss (D : XiTimePart65hPressureGapRayPotentialData)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    D.delta a - D.delta (a * b) = D.pressureLoss a b / ((a * b : ℕ) : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hab0 : (((a * b : ℕ) : ℝ)) ≠ 0 := by positivity
  have hmul : (((a * b : ℕ) : ℝ)) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.cast_mul a b
  unfold XiTimePart65hPressureGapRayPotentialData.delta
    XiTimePart65hPressureGapRayPotentialData.pressureLoss
  rw [hmul]
  field_simp [ha0, hab0]
  ring

private lemma delta_gap_eq_entropy (D : XiTimePart65hPressureGapRayPotentialData)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    D.delta a - D.delta (a * b) =
      (((b - 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)) * D.escortRenyiEntropy a b := by
  calc
    D.delta a - D.delta (a * b) = D.pressureLoss a b / ((a * b : ℕ) : ℝ) :=
      delta_gap_eq_pressureLoss D a b ha hb
    _ = (((b - 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)) *
          (D.pressureLoss a b / ((b - 1 : ℕ) : ℝ)) := by
      have hab0 : (((a * b : ℕ) : ℝ)) ≠ 0 := by positivity
      have hb10 : (((b - 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (show b - 1 ≠ 0 by omega)
      field_simp [hab0, hb10]
    _ = (((b - 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)) * D.escortRenyiEntropy a b := by
      congr 1
      unfold XiTimePart65hPressureGapRayPotentialData.pressureLoss
      rw [Nat.cast_sub (show 1 ≤ b by omega)]
      simpa using (D.escortRenyiIdentity a b ha hb).symm

private lemma delta_gap_nonneg (D : XiTimePart65hPressureGapRayPotentialData)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    0 ≤ D.delta a - D.delta (a * b) := by
  rw [delta_gap_eq_entropy D a b ha hb]
  have hfac : 0 ≤ (((b - 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)) := by positivity
  exact mul_nonneg hfac (D.escortRenyiNonneg a b ha hb)

private lemma delta_along_ray_tendsto_zero (D : XiTimePart65hPressureGapRayPotentialData)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    Tendsto (fun N => D.delta (a * b ^ N)) atTop (𝓝 0) := by
  have hsub :=
    (D.rayPressureRatioLimit a b ha hb).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => D.alphaStar) atTop (𝓝 D.alphaStar))
  simpa [XiTimePart65hPressureGapRayPotentialData.delta] using hsub

private lemma rayPartialSum_telescope (D : XiTimePart65hPressureGapRayPotentialData)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    ∀ N, D.rayPartialSum a b N = D.delta a - D.delta (a * b ^ N)
  | 0 => by
      simp [XiTimePart65hPressureGapRayPotentialData.rayPartialSum, pow_zero]
  | N + 1 => by
      have hbpos : 0 < b := by omega
      have hpow1 : 1 ≤ b ^ N := Nat.succ_le_of_lt (pow_pos hbpos N)
      have haN : 1 ≤ a * b ^ N := Nat.mul_le_mul ha hpow1
      have hmulpow : a * b ^ N * b = a * b ^ (N + 1) := by
        rw [pow_succ, Nat.mul_assoc]
      have hstep :
          D.rayTerm a b N = D.delta (a * b ^ N) - D.delta (a * b ^ (N + 1)) := by
        unfold XiTimePart65hPressureGapRayPotentialData.rayTerm
        have hgap := (delta_gap_eq_pressureLoss D (a * b ^ N) b haN hb).symm
        simpa [hmulpow] using hgap
      have ih := rayPartialSum_telescope D a b ha hb N
      rw [XiTimePart65hPressureGapRayPotentialData.rayPartialSum, Finset.sum_range_succ,
        show Finset.sum (Finset.range N) (fun x => D.rayTerm a b x) =
          D.delta a - D.delta (a * b ^ N) by simpa
            [XiTimePart65hPressureGapRayPotentialData.rayPartialSum] using ih,
        hstep]
      ring

/-- Paper label: `thm:xi-time-part65h-pressure-gap-ray-potential`. -/
theorem paper_xi_time_part65h_pressure_gap_ray_potential
    (D : XiTimePart65hPressureGapRayPotentialData) : D.pressureGapRayPotential := by
  intro a b ha hb
  refine ⟨delta_gap_eq_pressureLoss D a b ha hb, delta_gap_eq_entropy D a b ha hb,
    delta_gap_nonneg D a b ha hb, ?_⟩
  change Tendsto (fun N => D.rayPartialSum a b N) atTop (𝓝 (D.delta a))
  have hEq :
      (fun N => D.rayPartialSum a b N) = fun N => D.delta a - D.delta (a * b ^ N) := by
    funext N
    exact rayPartialSum_telescope D a b ha hb N
  rw [hEq]
  simpa using tendsto_const_nhds.sub (delta_along_ray_tendsto_zero D a b ha hb)

end Omega.Zeta
